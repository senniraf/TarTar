# -*- coding: utf-8 -*-
### BEGIN LICENSE
# Copyright (C) 2010 Mads Chr. Olesen <mchro@cs.aau.dk>, Kenneth Yrke Jørgensen <kyrke@cs.aau.dk>
#This program is free software: you can redistribute it and/or modify it 
#under the terms of the GNU General Public License version 3, as published 
#by the Free Software Foundation.
#
#This program is distributed in the hope that it will be useful, but 
#WITHOUT ANY WARRANTY; without even the implied warranties of 
#MERCHANTABILITY, SATISFACTORY QUALITY, or FITNESS FOR A PARTICULAR 
#PURPOSE.  See the GNU General Public License for more details.
#
#You should have received a copy of the GNU General Public License along 
#with this program.  If not, see <http://www.gnu.org/licenses/>.
### END LICENSE

import pyuppaal
import copy
import logging
import sys
logger = logging.getLogger('succgen')
from collections import defaultdict

from pyuppaal.ulp import lexer, parser, expressionParser

from opaal.model_parsers.state import State
import opaal.util
class UnknownVarTypeException(opaal.util.Error):
    pass
class VirtualMachineException(opaal.util.Error):
    pass
import util
from simplify import SimplifyModel
from analyzer import AnalyzeModel

from opaal.lattices.base_lattice import LatticeVector, BaseTimeLattice

# which externs can we use?
# name => (module, class)
available_externs = {
        'AbstractCache': ('opaal.lattices.abstract_cache', 'AbstractCache'),
        'UnionBitVector': ('opaal.lattices.bitvector', 'UnionBitVector'),
        'IntersectionBitVector': ('opaal.lattices.bitvector', 'IntersectionBitVector'),
        'MaxInteger': ('opaal.lattices.integer_lattice', 'MaxInteger'),
        'MinInteger': ('opaal.lattices.integer_lattice', 'MinInteger'),
        'DBMFederation': ('opaal.lattices.dbm', 'DBMFederation'),
        'DBMClock': ('opaal.lattices.dbm', 'DBMClock'),
        'DiscreteClock': ('opaal.lattices.discrete_clock', 'DiscreteClock'),
        }

class SuccessorGenerator:
    def __init__(self, model, constant_overrides=dict()):
        model = SimplifyModel(model, constant_overrides).simplify()

        self.model = model
        self.transitions = {}
        self.sync_transitions = {}
        self.dynamic_sync_transitions = {}
        self.templatename_to_idx = {}
        self.num_templates = len(self.model.templates)
        self.invariants = {}
        self.externs = {}

        self.analyzer = AnalyzeModel(model, constant_overrides)
        self.analyzer.analyze()

        #mapping from template => location id => nice name
        self.location_labels = defaultdict(dict)

        lex = lexer.lexer
        pars = parser.Parser(model.declaration, lex)

        declvisitor = parser.DeclVisitor(pars)
        declvisitor.visit(pars.AST)
        self.clocks = declvisitor.clocks

        self.constants = self.analyzer.constants

        #evaluate array dimensions to values
        self.variables = []
        for (vident, vtype, vdimensions, initval) in declvisitor.variables:
            for (dim, dim_idx) in zip(vdimensions, range(len(vdimensions))):
                vdimensions[dim_idx] = eval(util.expression_to_python(dim), {}, self.constants)
            if initval:
                initval = eval(util.expression_to_python(initval), {}, self.constants)
            elif vtype not in ['DBMFederation', 'DBMClock']:
                initval = 0
            self.variables += [(vident, vtype, vdimensions, initval)]

        #evaluate channel array dimensions to values
        self.channels = []
        self.channel_identifiers = []
        def crossproduct(vdimensions):
            if len(vdimensions) == 1:
                for i in xrange(vdimensions[0]):
                    yield "[%d]" % i
            else:
                for i in xrange(vdimensions[0]):
                    for t in crossproduct(vdimensions[1:]):
                        yield ("[%d]" % i) + t

        for (vident, vdimensions) in declvisitor.channels:
            self.channel_identifiers += [vident]
            if len(vdimensions) == 0:
                self.channels += [vident]
                continue
            for (dim, dim_idx) in zip(vdimensions, range(len(vdimensions))):
                vdimensions[dim_idx] = eval(util.expression_to_python(dim), {}, self.constants)
            for i in crossproduct(vdimensions):
                self.channels += [vident + i]

        #evaluate broadcast channel array dimensions to values
        self.broadcast_channels = []
        for (vident, vdimensions) in declvisitor.broadcast_channels:
            self.channel_identifiers += [vident]
            if len(vdimensions) == 0:
                self.broadcast_channels += [vident]
                continue
            for (dim, dim_idx) in zip(vdimensions, range(len(vdimensions))):
                vdimensions[dim_idx] = eval(util.expression_to_python(dim), {}, self.constants)
            for i in crossproduct(vdimensions):
                self.broadcast_channels += [vident + i]


        #import needed externs
        for ex in pars.externList:
            self._loadExtern(ex, pars)

        logger.info("Constants: %s", self.constants)
        logger.info("Variables: %s", self.variables)
        logger.info("Clocks: %s", self.clocks)
        logger.info("Externs: %s", self.externs)
        logger.info("Typedefs: %s", pars.typedefDict)
        logger.info("Channels: %s", self.channels)
        logger.info("Broadcast Channels: %s", self.broadcast_channels)

        #Calculate invariants
        for (t, t_idx) in zip(self.model.templates,
                            range(len(self.model.templates))):
            self.invariants[t_idx] = {}
            for (loc, l_idx) in zip(t.locations,
                                range(len(t.locations))):
                if (loc.invariant.value != None):
                    #the invariant should have the format:
                    # statement; ... ; statement; expression
                    #the statements are symbolic updates, while the
                    #expression is what determines if the invariant is satisfied
                    #example:
                    # dbm &= (dbm.x <= 5); not dbm.isEmpty()
                    #this should be backwards compatible.
                    s = loc.invariant.value.split(';')
                    statements = ";".join(s[:-1])
                    expression = util.expression_str_to_python(s[-1], self)
                    logger.debug("Invariant: '%s' ==> ('%s', '%s')", loc.invariant.value, statements, expression)

                    self.invariants[t_idx][l_idx] = (statements, expression)
                else:
                    self.invariants[t_idx][l_idx] = ("", "")

        #calculate transitions
        for (t, t_idx) in zip(self.model.templates, 
                            range(len(self.model.templates))):
            self.transitions[t_idx] = {}
            self.sync_transitions[t_idx] = {}
            self.dynamic_sync_transitions[t_idx] = {}
            self.templatename_to_idx[t.name] = t_idx

            for (loc, l_idx) in zip(t.locations,
                                range(len(t.locations))):
                if loc.name.get_value():
                    self.location_labels[t_idx][l_idx] = loc.name.get_value()

                self.transitions[t_idx][l_idx] = []
                self.sync_transitions[t_idx][l_idx] = {}
                self.dynamic_sync_transitions[t_idx][l_idx] = []
                for chan_name in self.channels:
                    self.sync_transitions[t_idx][l_idx][chan_name + "!"] = []
                    self.sync_transitions[t_idx][l_idx][chan_name + "?"] = []
                for chan_name in self.broadcast_channels:
                    self.sync_transitions[t_idx][l_idx][chan_name + "!"] = []
                    self.sync_transitions[t_idx][l_idx][chan_name + "?"] = []
                for tr in [tr for tr in t.transitions if tr.source == loc]:
                    target_idx = t.locations.index(tr.target)
                    debug_info = {}

                    guard_code = None
                    debug_info['guard_code'] = ''
                    if tr.guard.value != '':
                        logger.debug("Guard: %s", tr.guard.value)
                        logger.debug("==> %s", util.expression_str_to_python(tr.guard.value, self))
                        guard_code = compile(util.expression_str_to_python(tr.guard.value, self), "<guard>", 'eval')
                        debug_info['guard_code'] = tr.guard.value

                    update_code = None
                    debug_info['update_code'] = ''
                    if tr.assignment.value != '':
                        update_code = compile(util.statement_str_to_python(tr.assignment.value), "<update>", 'exec')
                        debug_info['update_code'] = tr.assignment.value

                    static_sync = False; sync_chan = None; sync_way = None
                    if tr.synchronisation.value != "":
                        logger.debug("Sync: %s", tr.synchronisation.value)
                        sync_way = tr.synchronisation.value.strip()[-1]
                        static_sync, sync_chan = util.channame_str_to_python_format_string(tr.synchronisation.value.strip()[:-1], self)
                        sync_chan += sync_way
                        logger.debug("==> (%s, %s)", static_sync, sync_chan)
                    
                    list_curtrans = [(target_idx, guard_code, update_code, 
                        sync_chan, debug_info)]

                    self.transitions[t_idx][l_idx] += list_curtrans

                    if static_sync:
                        self.sync_transitions[t_idx][l_idx][sync_chan] += list_curtrans
                    else:
                        self.dynamic_sync_transitions[t_idx][l_idx] += list_curtrans

        #print self.location_labels
        #print "Transitions:"
        #print self.transitions

    def _loadExtern(self, extname, pars):
        if extname in available_externs:
            modname, clsname = available_externs[extname]
        else: #try to load external extern
            externnode = pars.typedefDict[extname]
            #extract modname from AST node
            n = externnode.leaf
            modnames = []
            while n.type == 'Identifier' and \
                    len(n.children) == 2:
                modnames += [n.children[0]]
                n = n.children[1]
            modname = ".".join(modnames)
            clsname = n.children[0]
        __import__(modname)
        mod = sys.modules[modname]
        cls = getattr(mod, clsname)
        self.externs[extname] = cls


    def checkInvariant(self, state):
        for t_idx in self.invariants.keys():
            (cur_inv_statement, cur_inv) = self.invariants[t_idx][state.locs[t_idx]]
            if cur_inv_statement or cur_inv:
                # do symbolic update
                exec(cur_inv_statement, self.constants, state)
                #evaluate invariant
                if not eval(cur_inv, self.constants, state):
                    return False
        return True


    def trans_successors(self, state, trans_info=False):
        #Take an active transition
        for t_idx in xrange(self.num_templates):
            for (target_idx, guard, update, sync, debug_info) in self.transitions[t_idx][state.locs[t_idx]]:
                #Evaluate guard
                if guard:
                    logger.debug("Evaluating guard: %s on %s: ", debug_info['guard_code'], state)
                if guard == None or eval(guard, self.constants, state):
                    #If synchronisation, find trans to sync with
                    if sync:
                        if sync[-1] == '?':
                            #Only look for matching pair to ! syncs
                            continue
                        #expand channel name, if using variables
                        chan_name = sync[:-1] % state
                        brother_sync = chan_name + '?'

                        #TODO: also look at dynamic_sync_transitions, e.g. if "chan[N]?"
                        #2-Way handshake
                        if chan_name in self.channels:
                            for t2_idx in xrange(self.num_templates):
                                #the two synchronizers should be different
                                if t_idx == t2_idx:
                                    continue
                                for (target2_idx, guard2, update2, sync2, debug_info2) in self.sync_transitions[t2_idx][state.locs[t2_idx]][brother_sync]:
                                    if guard2 == None or eval(guard2, self.constants, state):
                                        #sync found
                                        a = state.copy()
                                        a.locs[t_idx] = target_idx
                                        a.locs[t2_idx] = target2_idx
                                        if update != None:
                                            try:
                                                exec update in self.constants, a
                                            except Exception, e:
                                                raise VirtualMachineException('Executing "' + debug_info['update_code'] + '": ' + str(e))
                                        if update2 != None:
                                            try:
                                                exec update2 in self.constants, a
                                            except Exception, e:
                                                raise VirtualMachineException('Executing "' + debug_info2['update_code'] + '": ' + str(e))
                                        if trans_info:
                                            a.trans_info = chan_name
                                        yield a
                        #broadcast handshake (can sync with 0..n receivers, 
                        #but all that can receive must)
                        elif chan_name in self.broadcast_channels:
                            a = state.copy()
                            a.locs[t_idx] = target_idx
                            bcast_updates = []
                            if update != None:
                                bcast_updates += [(update, debug_info)]
                            for t2_idx in xrange(self.num_templates):
                                #cannot sync with self
                                if t_idx == t2_idx:
                                    continue
                                for (target2_idx, guard2, update2, sync2, debug_info2) in self.sync_transitions[t2_idx][state.locs[t2_idx]][brother_sync]:
                                    if guard2 == None or eval(guard2, self.constants, state):
                                        #sync partner found
                                        #XXX, should we only move locations when doing updates?
                                        a.locs[t2_idx] = target2_idx
                                        if update2 != None:
                                            bcast_updates += [(update2, debug_info2)]
                            #do the updates
                            for (u, di) in bcast_updates:
                                try:
                                    exec u in self.constants, a
                                except Exception, e:
                                    raise VirtualMachineException('Executing "' + di['update_code'] + '": ' + str(e))
                            if trans_info:
                                a.trans_info = chan_name
                            yield a
                        else:
                            raise VirtualMachineException('Unsupported channel type for channel "%s"' % chan_name)
                    #Not synchronising
                    else:
                        a = state.copy()
                        a.locs[t_idx] = target_idx
                        #Execute update
                        logger.debug("Executing update: %s on %s: ", debug_info['update_code'], a)
                        if update != None:
                            try:
                                exec update in self.constants, a
                            except Exception, e:
                                raise VirtualMachineException('Executing "' + debug_info['update_code'] + '": ' + str(e))
                        #print "Result:", a.vars
                        if trans_info:
                            a.trans_info = ""
                        yield a
    
    def _apply_clock_max_const(self, state):
        """Apply max consts to clocks in state
        Modifies state in-place"""
        max_consts = self.analyzer.get_max_constants_for_state(state)
        for (c, cmax) in max_consts.iteritems():
            state[c].set_max_constant(cmax)

    def delay_successor_non_inclusive(self, state, trans_info=False):
        """Generate the delay successor, if it has effect, for time 
        implementations that cannot represent delay inclusively
        (e.g. DiscreteClock)."""
        a = state.copy()
        delay_has_effect = False
        for lc in a.lattice_part.values():
            if isinstance(lc, BaseTimeLattice):
                if lc.delay():
                    delay_has_effect = True
        if delay_has_effect:
            if trans_info:
                a.trans_info = ""
            return a
        else:
            return None

    def delay_successor_inclusive(self, state):
        """Generate the delay successor, for time implementations that can
        represent delay inclusively (e.g. DBM)"""
        a = state.copy()
        delay_has_effect = False
        for lc in a.lattice_part.values():
            if isinstance(lc, BaseTimeLattice):
                if lc.delay():
                    delay_has_effect = True
        if delay_has_effect:
            return a
        else:
            return None

    def successors(self, state, trans_info=False):
        for a in self.trans_successors(state, trans_info=trans_info):
            if self.checkInvariant(a):
                self._apply_clock_max_const(a)
                #logger.debug("Returning %s", a)
                yield a
        #XXX, chose delay_successor implementation cleverly
        a = self.delay_successor_non_inclusive(state, trans_info=trans_info)
        if a and self.checkInvariant(a):
            self._apply_clock_max_const(a)
            #logger.debug("Returning %s", a)
            yield a

    def get_initialstate(self):
        #define own subclass of State
        class PyuppaalState(State):
            succgen = self
            def __init__(self):
                State.__init__(self)

        #calculate initial state
        initstate = PyuppaalState()

        #Set initial locationvectior
        for (idx, t) in enumerate(self.model.templates):
            initstate.locs[idx] = t.locations.index(t.initlocation)
        #Set initial vars
        for (var, vartype, array_dimensions, initval) in self.variables:
            if vartype in self.externs:
                initval = None
                #Lattice type
                initval = self.externs[vartype](name=var, dimensions=array_dimensions, context=self)
                if initval:
                    initstate.lattice_part[var] = initval
            else:
                #XXX convert to numpy?
                if array_dimensions == []:
                    initstate[var] = initval
                else:
                    curval = initval
                    for dim in reversed(array_dimensions):
                        new_val = []
                        for i in range(dim):
                            new_val.append(copy.deepcopy(curval))
                        curval = new_val
                    initstate[var] = curval
        #Set initial clocks (use default implementation for clock: DiscreteClock)
        #(we only get here if clock has not been typedef'ed)
        for (c, cmax) in self.clocks:
            if not "DiscreteClock" in self.externs:
                self._loadExtern('DiscreteClock', None)
            #XXX, dimensions?
            initval = self.externs['DiscreteClock'](name=c, dimensions=[], context=self)
            if initval:
                initstate.lattice_part[c] = initval


        #do delay
        initstate.may_delay()

        #apply invariants
        if not self.checkInvariant(initstate):
            raise VirtualMachineException("Initial state disallowed by invariants!")

        logger.info("Initial state: locs: %s vars: %s lattice_part: %s", initstate.locs, initstate.vars, initstate.lattice_part)
        return initstate

    def is_variable(self, identifier):
        if identifier in [name for (name, _, _, _) in self.variables]:
            return True

        return False



# vim:ts=4:sw=4:expandtab
