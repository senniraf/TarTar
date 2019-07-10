# -*- coding: utf-8 -*-
### BEGIN LICENSE
# Copyright (C) 2010 Mads Chr. Olesen <mchro@cs.aau.dk>, Andreas Dalsgaard <andrease@cs.aau.dk>
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
logger = logging.getLogger('gensuccgen')
from collections import defaultdict
import ctypes
from ctypes import *
import tempfile
import os
import subprocess

from pyuppaal.ulp import lexer, parser, expressionParser, systemdec_parser
import pydbm

import opaal.util
import util
from simplify import SimplifyModel
from analyzer import AnalyzeModel

# which externs can we use?
# name => (module, class)
available_externs = {
        'UnionBitVector': ('opaal.clattices.bitvector', 'UnionBitVector'),
        'ApronOctagon': ('opaal.clattices.apron', 'ApronOctagon'),
        }

class GenerateSuccessorGenerator:

    """
    Generate a C-file, that can generate the statespace of the model.
    The C-file should be compatible with LTSmin 
    (http://fmt.cs.utwente.nl/tools/ltsmin/)
    """
    def __init__(self, model, constant_overrides=dict(), extrapolation="LU"):
        """
        @extrapolation can either be "k" for max k-constant extrapolation or
            "LU" for Lower/upper bound extrapolation.
        """
        model = SimplifyModel(model, constant_overrides).simplify()

        self.edge_label_list = []
        #constains all synchronization labels
        self.chan_label_list = {}
        self.chan_counter = 0

        self.model = model
        self.transitions = {}
        self.sync_transitions = {}
        self.dynamic_sync_transitions = {}
        self.templatename_to_idx = {}
        self.num_templates = len(self.model.templates)
        self.priority_groups = []
        self.invariants = {}
        self.externs = {}
        self.local_variables = []
        self.ofilelib = None
        self.extrapolation = extrapolation
        self.varTypes = {}

        self.analyzer = AnalyzeModel(model, constant_overrides)
        self.analyzer.analyze()

        #mapping from template => location id => nice name
        self.location_labels = defaultdict(dict)
        self.declvisitor = self.analyzer.declvisitor
        declvisitor = self.declvisitor
        pars = declvisitor.parser
        self.pars = pars

        self.clocks = declvisitor.clocks
        self.clock_indexes = ["0clock"] + [c for (c, _) in self.clocks]
        
        self.constants = self.analyzer.constants
        self.simplyfied_struct_name = {} #Mapping from simplyfied struct variable name to originating struct type (used for struct return types)
        self.structs = {} #Mapping from struct name to list of vardecl
        self.pars.identifierTypeDict = self.pars.globalIdentifierTypeDict
        ptypedefs = declvisitor.preprocess_typedefs()

        for (typename, ptypedef) in ptypedefs.items():
            vdecl_list = []
            for pvardecl in ptypedef:
                util.eval_vardecl_expressions(pvardecl, self.constants, do_eval_initval=True)
                vdecl_list.append(pvardecl)
            self.structs[typename] = vdecl_list

        #import needed externs
        for ex in pars.externList:
            self._loadExtern(ex, pars)

        # variables = discrete_variables \cup lattice_variables
        self.variables = []
        self.discrete_variables = []
        self.lattice_variables = []
        for vdecl in declvisitor.variables:
            vident = vdecl.identifier; vtype = vdecl.vartype
            vdimensions = vdecl.eval_dimensions

            self.variables += [vdecl]
            if isinstance(vtype, str) and vtype in self.externs: 
                assert vdecl.eval_initval == None
                #create lattice variable code generation object
                lattice_obj = self.externs[vtype](name=vident, dimensions=vdimensions, context=self)
                self.lattice_variables += [lattice_obj]
            #extern child thingy
            elif isinstance(vtype, list) and self.is_lattice_variable(vtype[0]):
                lattice_obj = self.get_lattice_variable(vtype[0])
                lattice_obj.addChildVariable(vtype[1:], vident, vdimensions)
            elif vdecl.identifier in self.clock_indexes:
                continue 
            elif util.is_struct_type(vtype, self.structs):
                for svdecl in util.getStructVarDecl(vdecl, self.structs, self.constants, vdecl.identifier):
                    self.discrete_variables += [svdecl]
                self.simplyfied_struct_name[vdecl.identifier] = vdecl.vartype
            else:
                self.discrete_variables += [vdecl]

        #evaluate channel array dimensions to values
        def crossproduct(vdimensions):
            if len(vdimensions) == 1:
                for i in xrange(vdimensions[0]):
                    yield "[%d]" % i
            else:
                for i in xrange(vdimensions[0]):
                    for t in crossproduct(vdimensions[1:]):
                        yield ("[%d]" % i) + t

        def evaluate_channel_array_dimensions(decl_channels, channel_list):
            for (vident, vdimensions) in decl_channels:
                self.channel_identifiers += [vident]
                channel_list.append(vident)
                if len(vdimensions) == 0:
                    channel_list.append(vident)
                    continue
                for (dim_idx, dim) in enumerate(vdimensions):
                    vdimensions[dim_idx] = eval(util.expression_to_python(dim), {}, self.constants)
                for i in crossproduct(vdimensions):
                    channel_list.append(vident + i)

        self.channel_identifiers = []

        self.channels = []
        evaluate_channel_array_dimensions(declvisitor.channels, self.channels)
        self.urgent_channels = []
        evaluate_channel_array_dimensions(declvisitor.urgent_channels, self.urgent_channels)
        self.broadcast_channels = []
        evaluate_channel_array_dimensions(declvisitor.broadcast_channels, self.broadcast_channels)
        self.urgent_broadcast_channels = []
        evaluate_channel_array_dimensions(declvisitor.urgent_broadcast_channels, self.urgent_broadcast_channels)

        #we only get clocks, if "clock" has not been typedef'ed
        self.usesDBM = (self.clocks != [])

        #XXX, one extern or using DBMs
        assert len(self.externs) <= 1 or not self.usesDBM

        logger.info("Constants: %s", self.constants)
        logger.info("Variables: %s", self.variables)
        logger.info("Clocks: %s", self.clocks)
        logger.info("Externs: %s", self.externs)
        logger.info("Typedefs: %s", pars.typedefDict)
        logger.info("Channels: %s", self.channels)
        logger.info("Urgent Channels: %s", self.urgent_channels)
        logger.info("Broadcast Channels: %s", self.broadcast_channels)

        #Calculate invariants
        for (t_idx, t) in enumerate(self.model.templates):
            self.invariants[t_idx] = {}
            for (l_idx, loc) in enumerate(t.locations):
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
                    if not statements:
                        statements = "/* nop */"
                    else:
                        statements = util.statement_str_to_c(statements, self)
                    expr = util.invariant_str_to_c(s[-1], self, "out")
                    logger.debug("Invariant: '%s' ==> ('%s', '%s')", loc.invariant.value, statements, expr)

                    self.invariants[t_idx][l_idx] = (statements, expr)
                else:
                    self.invariants[t_idx][l_idx] = ("", "")

        #calculate transitions
        for (t_idx, t) in enumerate(self.model.templates):
            self.transitions[t_idx] = {}
            self.sync_transitions[t_idx] = {}
            self.dynamic_sync_transitions[t_idx] = {}
            self.templatename_to_idx[t.name] = t_idx

            for (l_idx, loc) in enumerate(t.locations):
                if loc.name.get_value():
                    self.location_labels[t_idx][l_idx] = loc.name.get_value()

                self.transitions[t_idx][l_idx] = []
                self.sync_transitions[t_idx][l_idx] = {}
                self.dynamic_sync_transitions[t_idx][l_idx] = {}
                for chan_name in self.channels:
                    self.sync_transitions[t_idx][l_idx][chan_name + "!"] = []
                    self.sync_transitions[t_idx][l_idx][chan_name + "?"] = []
                for chan_name in self.urgent_channels:
                    self.sync_transitions[t_idx][l_idx][chan_name + "!"] = []
                    self.sync_transitions[t_idx][l_idx][chan_name + "?"] = []
                for chan_name in self.broadcast_channels:
                    self.sync_transitions[t_idx][l_idx][chan_name + "!"] = []
                    self.sync_transitions[t_idx][l_idx][chan_name + "?"] = []
                for chan_name in self.urgent_broadcast_channels:
                    self.sync_transitions[t_idx][l_idx][chan_name + "!"] = []
                    self.sync_transitions[t_idx][l_idx][chan_name + "?"] = []
                for chan_name in self.channel_identifiers:
                    self.dynamic_sync_transitions[t_idx][l_idx][chan_name + "!"] = []
                    self.dynamic_sync_transitions[t_idx][l_idx][chan_name + "?"] = []
                for tr in [tr for tr in t.transitions if tr.source == loc]:
                    target_idx = t.locations.index(tr.target)
                    debug_info = {}

                    guard_code = "true"
                    debug_info['guard_code'] = ''
                    if tr.guard.value != '':
                        logger.debug("Guard: %s", tr.guard.value)
                        guard_code = util.expression_str_to_c(tr.guard.value, self) #TODO add check that functions do not have side effects
                        logger.debug("==> %s", guard_code)
                        debug_info['guard_code'] = tr.guard.value

                    update_code = "/* nop */"
                    debug_info['update_code'] = ''
                    if tr.assignment.value != '':
                        update_code = util.statement_str_to_c(tr.assignment.value, self)
                        debug_info['update_code'] = tr.assignment.value
                    #convert clock expressions to fed updates
                    fed_update = "/* nop */"
                    if tr.guard.value != '':
                        fed_update = util.expression_str_to_fedupdate_c(tr.guard.value, self)
                        logger.debug("fed==> %s", fed_update)

                    static_sync = False; sync_chan = None; sync_way = None; index_exprs = []
                    if tr.synchronisation.value != "":
                        logger.debug("Sync: %s", tr.synchronisation.value)
                        sync_way = tr.synchronisation.value.strip()[-1]
                        sync_chan, index_exprs = util.channame_str_to_index_cexprs(tr.synchronisation.value.strip()[:-1], self)
                        sync_chan += sync_way
                        static_sync = (index_exprs == [])
                        logger.debug("==> (%s, %s)", sync_chan, index_exprs)
                    
                    list_curtrans = [(target_idx, guard_code, update_code, fed_update, 
                        (sync_chan, index_exprs), debug_info)]

                    self.transitions[t_idx][l_idx] += list_curtrans

                    if static_sync:
                        self.sync_transitions[t_idx][l_idx][sync_chan] += list_curtrans
                    elif index_exprs != []:
                        self.dynamic_sync_transitions[t_idx][l_idx][sync_chan] += list_curtrans

        self.calculatePriorityGroups()

        self.global_functions = declvisitor.functions
        print(self.sync_transitions);

    def _loadExtern(self, extname, pars):
        if extname in available_externs:
            modname, clsname = available_externs[extname]
        else: #try to load external extern
            externnode = pars.typedefDict[extname]
            #extract modname from AST node
            n = externnode.leaf
            modnames = []
            while n.type == 'Identifier' and \
                    len(n.children) == 1:
                modnames += [n.leaf]
                n = n.children[0]
            modname = ".".join(modnames)
            clsname = n.leaf
        __import__(modname)
        mod = sys.modules[modname]
        cls = getattr(mod, clsname)
        self.externs[extname] = cls

    def calculatePriorityGroups(self):
        try:
            pars = systemdec_parser.SystemDeclarationParser(self.model.system)
        except:
            opaal.util.emergencyExitSystemDecl("A parsing error occurred when parsing the system declaration/definition of the model.")
        res = pars.AST

        systemsnode = [c for c in res.children if c.type == 'System'][0]

        prevprio = 0
        cur_group = []
        for inst in systemsnode.children:
            prio = inst.priority
            ident = inst.leaf
            tname = ident.children[0]
            temp = [t for t in self.model.templates if t.name == tname][0]
            if prevprio != prio:
                if len(cur_group):
                    self.priority_groups += [cur_group]
                    cur_group = []
            prevprio = prio
            cur_group += [temp]
        if len(cur_group):
            self.priority_groups += [cur_group]
            cur_group = []

        logger.info("Priority groups: %s", 
                [[t.name for t in g] for g in self.priority_groups])

    #{{{ Generate C code methods
    def generateCFile(self, outfile):
        parts = []

        # Header {{{
        header = """#include <stdio.h>
#include <string.h>
#include <stdint.h>
#include <assert.h>
#include <bitset>
#include <iostream>

typedef uint64_t ulong_long_int_t;
typedef int64_t slong_long_int_t;
typedef uint32_t ulong_int_t;
typedef int32_t slong_int_t;
typedef union
{
    uint16_t var;
    uint32_t __padding__;
} ushort_int_t;
typedef union
{
    int16_t var;
    uint32_t __padding__;
} sshort_int_t;
typedef union
{
    uint8_t var;
    uint32_t __padding__;
} ubyte_t;
typedef ubyte_t byte_t;
typedef union
{
    int8_t var;
    uint32_t __padding__;
} sbyte_t;
typedef union
{
    uint8_t var;
    uint32_t __padding__;
} bool_t;
typedef size_t size_int_t;

typedef struct transition_info
{
    int* label;
    int  group;
} transition_info_t;
"""
        dbmheader = """
#include "dbm/fed.h"
#include "dbm/ClockAccessor.h"
"""

        parts += [header]
        if self.usesDBM:
            parts += [dbmheader]
        elif len(self.externs):
            assert len(self.lattice_variables) == 1, "XXX multiple lattice vars not supported"
            for lat_obj in self.lattice_variables:
                parts += [lat_obj.generateHeader() + "\n"]
        #}}}
        parts += ["\n"]
        parts += [self.generateConstants(self.constants)]
        parts += ["\n"]
        parts += [self.generateVarTypeArray()]
        parts += ["\n"]
        parts += [self.generateStateStruct()]
        parts += ["\n"]
        parts += [self.generateGlobalVariablesForStructReturnTypes(self.structs)]
        parts += ["\n\n"]
        if self.usesDBM or len(self.externs):
            parts += [self.generateLatticeFunctions()]
            parts += ["\n"]
        parts += [self.generateCoverFunction()]
        parts += ["\n"]
        parts += [self.generateJoinFunction()]
        parts += ["\n"]
        parts += [self.generateFunctions()]
        parts += ["\n"]
        parts += [self.generate_committed_bitsets()]
        parts += ["\n"]
        parts += [self.generate_state_has_outgoing_enabled_urgent_sync()]
        parts += ["\n"]
        parts += [self.generate_urgent_bitsets()]
        parts += ["\n"]
        parts += [self.generateInitialState()]
        parts += ["\n"]
        if self.extrapolation == "k":
            parts += [self.generate_extrapolate_max_constants()]
            parts += ["\n"]
        elif self.extrapolation == "LU":
            parts += [self.generate_extrapolate_lu_bounds()]
            parts += ["\n"]
        else:
            assert False, "Unknown extrapolation type!"
        parts += [self.generate_clock_rates()]
        parts += ["\n"]
        parts += [self.generate_apply_invariants()]
        parts += ["\n"]
        parts += [self.generateInitialFuncs()]
        parts += ["\n"]
        parts += [self.generate_lattice_support_funcs()]
        parts += ["\n"]
        # generate_label_funcs moved from here
        parts += [self.generate_do_callback()]
        parts += ["\n"]
        parts += [self.generate_get_successors()]
        parts += ["\n"]
        parts += [self.generate_label_funcs()]
        parts += ["\n"]
        parts += [self.generateStubs()]
        parts += ["\n"]
        # Fake main for debugging {{{
        if self.usesDBM:
            parts += ["""
void dummy_cb(void *arg, transition_info_t *transition_info, state_struct_t *out) {
	printf("succ_cb: %p\\n", out->fed);
	std::cout << "succ_cb: " << out->fed->toString(clockNames) << std::endl;
}

int main() {
    //g++ -g -shared -O0 -fPIC -I/usr/local/uppaal/include/ -L/usr/local/uppaal/lib/ -o gensuccgen gensuccgen.cpp -ludbm
    state_struct_t *s1 = (state_struct_t*)malloc(get_state_size());
    get_initial_state(s1);
	std::cout << "initial: " << s1->fed->toString(clockNames) << std::endl;

	get_successors(NULL, s1, dummy_cb, NULL);

    return 0;
}
"""]
        elif len(self.externs) == 1 and self.externs.has_key("ApronOctagon"):
            parts += ["""
void dummy_cb(void *arg, transition_info_t *transition_info, state_struct_t *out) {
	printf("succ_cb: %p\\n", out->oct);
	std::cout << "succ_cb: " << lattice_print(out->oct) << std::endl;
}

int main() {
    //g++ -g -shared -O0 -fPIC -I/usr/local/uppaal/include/ -L/usr/local/uppaal/lib/ -o gensuccgen gensuccgen.cpp -ludbm
    state_struct_t *s1 = (state_struct_t*)malloc(get_state_size());
    get_initial_state(s1);
	std::cout << "initial: " << lattice_print(s1->oct) << std::endl;

	get_successors(NULL, s1, dummy_cb, NULL);

    return 0;
}
"""]
        #}}}
        parts += ["/* vim:ts=4:sw=4:noexpandtab */\n"]

        outfile.write("".join(parts))

    def generateConstants(self, constants):
        parts = []
        for (c, cval) in constants.iteritems():
            parts += ["const uint32_t %s = %d;\n" % (c, cval)]
        return "".join(parts)
    
    def generateGlobalVariablesForStructReturnTypes(self, structs):
        parts = []
        for (typeName, _) in structs.iteritems():
            vdeclList = util.getStructVarDeclInternal(typeName, None, typeName, [], self.structs, self.constants, typeName)
            (_, var_parts) = util.makeVariableList(vdeclList, False, True)
            parts.append('//global variables for type: %s\n %s;' % (typeName, ';'.join(var_parts)))

        return "".join(parts)

    def getFieldsSize(self, fields):
        """
        Calculate how many 32-bit integers are in the fields list.
        This is needed as LTSmin needs the number of 32-bit ints in the state
        vector.
        """
        size = 0

        for (_, ctype) in fields:
            if ctype in (ctypes.c_uint32, ctypes.c_int32):
                size += 1 
            elif ctype.__class__.__name__ == 'PyCArrayType':
                #XXX Alfons had a crash with 'ArrayType', different ctypes version?
                size += len(ctype())
            elif ctype == ctypes.c_void_p:
                size += sizeof(c_voidp)/4
            else:
                print ctype.__class__.__name__
                assert False

        return size

    def generateVarTypeArray(self):
        parts = []
        varTypeList = []

        for vdecl in self.discrete_variables:
            varTypeList.append(util.vardecl_to_ctype(vdecl))

        parts += ["static const char* var_types[] = {\n"]
        i = 0
        for x in list(set(varTypeList)):
            parts += ['\t"%s",\n' % ( x )]
            self.varTypes[x] = i
            i += 1

        #we always want an uint32_t, to e.g. have the lattice vars as this type
        if "uint32_t" not in self.varTypes:
            self.varTypes["uint32_t"] = i
            i += 1
            parts += ['\t"uint32_t",\n']

        #Add a type for each template(/process due to simplifier)
        for template in self.model.templates:
            parts += ['\t"%s",\n' % ( template.name )]
            self.varTypes[template.name] = i
            i += 1

        parts += ['\t""\n};\n']
        return "".join(parts)

    
    #Should be called after generateVarTypeArray
    def lookup_type_id(self, type_str):
        return self.varTypes[type_str]

    def generateStateStruct(self):
        parts = ["""struct state_struct_t
{
"""]
        (var_list, var_parts) = util.makeVariableList(self.discrete_variables, False)
        parts += ';\n'.join(var_parts)
        parts += ';\n'
        ctype_structfields = var_list
        lattice_field_name = ""

        # Locations {{{
        for (idx, t) in enumerate(self.model.templates):
            parts += ["\tuint32_t %s;\n" % (t.name)]
            ctype_structfields += [(t.name, ctypes.c_uint32)]
        #}}}
        # Symbolic lattice part {{{
        if self.usesDBM:
            parts += ["\tdbm::fed_t *fed;\n"]

            #pointer for DBM fed
            ctype_structfields += [('fed', ctypes.c_void_p)]
            lattice_field_name = "fed"
        elif len(self.externs):
            assert len(self.lattice_variables) == 1, "XXX multiple lattice vars not supported"
            for lat_obj in self.lattice_variables:
                parts += ["\t" + lat_obj.generateStateStructPart() + "\n"]
                ctype_structfields += [(lat_obj.name, ctypes.c_void_p)]
                lattice_field_name = lat_obj.name
		#}}}

        parts += ["""}
__attribute__((__packed__));\n"""]
        parts += ["int state_size = sizeof(state_struct_t);\n"]
        if self.usesDBM:
            parts += ["#define lattice_part(a) a->fed\n"]
        elif len(self.externs):
            parts += ["#define lattice_part(a) a->%s\n" % (lattice_field_name)]


        class StateStruct(ctypes.Structure):
            _pack_ = 1 #the struct is packed!
            _fields_ = ctype_structfields
            succgen = self
            lat_field_name = lattice_field_name

            def __hash__(self):
                #XXX hash for real!
                return 42

            def __copy__(self):
                ret = self.__class__()
                for (fname, _) in self._fields_:
                    setattr(ret, fname, getattr(self, fname))
                if self.succgen.usesDBM:
                    ret.py_fed = copy.copy(self._get_pyfed_from_state())
                    ret.fed = long(ret.py_fed._fed.this)
                #other lattice types
                elif len(self.succgen.externs):
                    setattr(ret, self.lat_field_name,
                            self.succgen._get_object_file().lattice_clone(
                                c_void_p(getattr(self, self.lat_field_name))
                                )
                            )
                return ret


            def __eq__(self, other):
                if not self.discrete_eq(other):
                    return False
                if self.succgen.usesDBM:
                    fed_py1 = self._get_pyfed_from_state()
                    fed_py2 = other._get_pyfed_from_state()
                    return fed_py2 <= fed_py1 and fed_py1 <= fed_py2
                elif len(self.succgen.externs):
                    return bool(self.succgen._get_object_file().covered_by(byref(other), byref(self))) and \
                        bool(self.succgen._get_object_file().covered_by(byref(self), byref(other)))
                else:
                    return True

            def __getitem__(self, key):
                """To make StateStruct class compatible with old opaal interface,
                which will call with something like s['locs'][2] to get locations,
                or s['varname'] to get variable values."""
                if type(key) == int:
                    return getattr(self, self._fields_[key][0])
                elif key == "locs":
                    #XXX, yuck, deprecate locs access
                    class LocationAccessor(object):
                        def __init__(self, state):
                            self.state = state

                        def __getitem__(self, loc_key):
                            for (t_idx, t) in enumerate(self.state.succgen.model.templates):
                                if t_idx == loc_key:
                                    return getattr(self.state, t.name)
                    return LocationAccessor(self)
                return getattr(self, key)

            def discrete_eq(self, other):
                for (t_idx, t) in enumerate(self.succgen.model.templates):
                    if getattr(self, t.name) != getattr(other, t.name):
                        return False
                for (fname, _, _, _) in self.succgen.discrete_variables:
                    if getattr(self, fname) != getattr(other, fname):
                        return False
                return True

            def covers(self, other):
                """Cover relation: a covers b <=> a.discrete == b.discrete and a.lattice covers b.lattice"""
                if self.discrete_eq(other):
                    if self.succgen.usesDBM:
                        fed_py1 = self._get_pyfed_from_state()
                        fed_py2 = other._get_pyfed_from_state()
                        return fed_py2 <= fed_py1
                    elif len(self.succgen.externs):
                        return bool(self.succgen._get_object_file().covered_by(byref(other), byref(self)))
                    else:
                        return True
                return False

            def join(self, other):
                """Returns new state that is the join of self and other"""
                assert self.discrete_eq(other), "Must be discrete equal for joining"
                res = copy.copy(self)
                if len(self.succgen.externs):
                    self.succgen._get_object_file().join_with(byref(res), byref(other))
                return res
        
            def _get_pyfed_from_state(self):
                if not self.succgen.usesDBM:
                    return None
                if hasattr(self, "py_fed"):
                    return self.py_fed
                fed_py = pydbm.udbm.Federation(self.succgen.clockContext)
                fed_py._fed = pydbm.udbm_int.fed_t_pointer_to_Federation(self.fed)
                self.py_fed = fed_py
                return self.py_fed

            def __str__(self):
                loc_labels = []
                for (t_idx, t) in enumerate(self.succgen.model.templates):
                    l_idx = getattr(self, t.name)
                    loc_labels.append(t.name + ": " + self.succgen.location_labels[t_idx].get(l_idx, str(l_idx)))
                loc_labels = "(" + ", ".join(loc_labels) + ")"

                var_labels = []
                for vdecl in self.succgen.discrete_variables:
                    var = vdecl.identifier
                    val = getattr(self, var)
                    var_labels.append(var + ": " + str(val))
                var_labels = "(" + ", ".join(var_labels) + ")"

                if self.succgen.usesDBM:
                    fed_py = self._get_pyfed_from_state()
                    return "(" + loc_labels + ", " + var_labels + ", " + str(fed_py) + ")"
                elif len(self.succgen.externs):
                    lattice_str = string_at(self.succgen._get_object_file().lattice_print(
                        c_void_p(getattr(self, self.lat_field_name))
                        ))
                    return "(" + loc_labels + ", " + var_labels + ", " + lattice_str + ")"
                else:
                    return "(" + loc_labels + ", " + var_labels + ")"



        self.StateStruct = StateStruct
        self.cbfunc = ctypes.CFUNCTYPE(None, #return type
                ctypes.c_void_p, #arg
                ctypes.c_void_p, #trans_info_t
                ctypes.POINTER(StateStruct) #state_struct_t
                )

        #generate ClockAccessor subclass for dbm
        if self.usesDBM:
            self.clockContext = pydbm.Context([c for (c, _) in self.clocks])
            parts += ["""
class ClockNamesAccessor: public dbm::ClockAccessor {
public:
    virtual const std::string getClockName(cindex_t i) const {
        switch (i) {
"""]

            for (c_idx, (c, _)) in enumerate(self.clocks):
                parts += ["\t\t\tcase %d: return std::string(\"%s\");\n\t\t\tbreak;\n" % (c_idx+1, c)]
            parts += ["""
        }
    }
};
static ClockNamesAccessor clockNames = ClockNamesAccessor();
"""]

        parts += ["""
extern "C" int get_state_variable_count() 
{
    return %d;
}
""" % self.getFieldsSize(self.StateStruct._fields_)]

        parts += ["""
extern "C" const char* get_state_variable_name(int var)
{
    switch (var)
    {
"""]
        i = 0
        for (var, ctype) in self.StateStruct._fields_:
            if ctype.__class__.__name__ == 'PyCArrayType':
                for j in range(len(ctype())):
                    parts += ["\t\tcase %d: return \"%s[%d]\";\n" % (i, var, j)]
                    i += 1
            elif self.usesDBM and var == "fed":
                #calculate how many 32-bit integers goes to a pointer
                for j in range(sizeof(c_voidp)/4):
                    parts += ["\t\tcase %d: return \"%s%d\";\n" % (i, var, i)]
                    i += 1
            elif ctype == c_void_p:
                #calculate how many 32-bit integers goes to a pointer
                for j in range(sizeof(c_voidp)/4):
                    parts += ["\t\tcase %d: return \"%s%d\";\n" % (i, var, i)]
                    i += 1
            else:
                parts += ["\t\tcase %d: return \"%s\";\n" % (i, var)]
                i += 1

        parts += ["""
        default:
            return NULL;
    }
}
"""]


        parts += ["""
extern "C" int get_state_variable_type(int var)
{
    switch (var)
    {
"""]
        i = 0
        #XXX this does NOT handle arrays properly, should maybe iterate over this:
        #for (var, ctype) in self.StateStruct._fields_:
        for vdecl in self.discrete_variables:
            varType = vdecl.vartype; varDimensions = vdecl.eval_dimensions
            if varDimensions == []:
                parts += ['\t\tcase %d: return %d;\n' % (i, self.lookup_type_id(util.vardecl_to_ctype(vdecl)))]
                i += 1
            else: 
                elements = 1
                for t in varDimensions:
                    elements = elements * t

                for j in range(elements):
                    parts += ['\t\tcase %d: return %d;\n' % (i, self.lookup_type_id(util.vardecl_to_ctype(vdecl)))]
                    i += 1
        
        for template in self.model.templates:
            #XXX reverted to ints, as temporary workaround to have LTSmin queries work
            #parts += ['\t\tcase %d: return %d;\n' % (i, self.lookup_type_id(template.name) )]
            parts += ['\t\tcase %d: return %d;\n' % (i, 0)]
            i += 1

        #Fed
        if self.usesDBM:
            parts += ['\t\tcase %d: return %d;\n' % (i, 0 )]
            i += 1
            parts += ['\t\tcase %d: return %d;\n' % (i, 0 )]
        elif len(self.externs):
            parts += ['\t\tcase %d: return %d;\n' % (i, self.lookup_type_id("uint32_t") )]
            i += 1
            parts += ['\t\tcase %d: return %d;\n' % (i, self.lookup_type_id("uint32_t") )]


        parts += ["""
        default:
            return 0;
    }
}
"""]

        parts += ["""
extern "C" int get_state_variable_type_count() 
{
    return %d;
}
""" % len(self.varTypes)]

        parts += ["""
extern "C" const char* get_state_variable_type_name(int type) 
{
    assert(type < %d && "get_state_variable_type_name: invalid type");
    return var_types[type];
}
""" % (len(self.varTypes))]
        parts += ["""
extern "C" int get_state_variable_type_value_count(int type)
{
    switch (type)
    {
"""]
        i = 0
        parts += ['\tcase %d: return 0;\n' % i]
        i += 1

        for template in self.model.templates:
            parts += ['\tcase %d: return %d;\n' % (i, len(template.locations))]
            i += 1

        parts += ["""
    };

    return 0;
}"""]
        parts += ["""
extern "C" const char* get_state_variable_type_value(int type, int value) 
{
    switch (type)
    {
"""]
        i = 0
        #parts += ['\t\tcase %d: return "int stub";\n' % i]    
        i += 1

        for template in self.model.templates:
            parts += ['\t\tcase %d:\n' % i]
            parts += ['\t\t\tswitch (value)\n\t\t\t{\n']
            j = 0
            for location in template.locations:
                try:
                    if location.name.value != None:
                        parts += ['\t\t\t\tcase %d: return "%s";\n' % (j, location.name.value)]
                    else:
                        raise Exception("Location does not have name")                        
                except:
                    parts += ['\t\t\t\tcase %d: return "%s_L%d";\n' % (j, template.name, j)]
            
                j += 1
            parts += ['\t\t\t};\n']
            i += 1
        
        parts += ['\t};\n']
        parts += ['\treturn "";\n']
        parts += ["""
}
"""]
        num_trans_total = sum(map(len, [temp.transitions for temp in self.model.templates]))
        parts += ["""
extern "C" int get_transition_count() 
{
    return %d;
}
""" % num_trans_total]



        return "".join(parts)

    def generateLatticeFunctions(self):
        parts = ["""extern "C" const char *lattice_print(void *l)
{
"""]
        if self.usesDBM:
            parts += "\treturn ((dbm::fed_t*)l)->toString(clockNames).c_str();";
        elif len(self.externs):
            for lat_obj in self.lattice_variables:
                parts += ["\t" + lat_obj.generateLatticePrintPart("l") + "\n"]
        parts += ["""
}
""" ]
        if len(self.externs):
            for lat_obj in self.lattice_variables:
                parts += [lat_obj.generateExtraLatticeFunctions()]
        return "".join(parts)

    def generateFunctions(self):
        cfunctions = []
        
        ### XXX to work around DeclVisitor strucktur 
        ### seems like it should take a AST and something to handel clocks and be moved
        ### to opaal instead of having the visitor pattern for the "compiler" in the parser
        class FakeParser:
            def __init__(self, AST, typedefDict, funcIdentifierTypeDict):
                self.AST = AST
                self.typedefDict = typedefDict
                self.identifierTypeDict = funcIdentifierTypeDict

        class FuncSuccGen:
            def __init__(self, succgen, func_variables, parameter_variables, func_constants, structs, simplyfied_struct_name = {}):
                self.succgen = succgen
                self.pars = succgen.pars
                self.variables = succgen.variables
                self.discrete_variables = succgen.discrete_variables
                self.lattice_variables = succgen.lattice_variables
                self.local_variables = func_variables
                self.parameter_variables = parameter_variables            
                self.constants = dict(succgen.constants.items() + func_constants.items())
                self.clocks = succgen.clocks
                self.clock_indexes = succgen.clock_indexes
                self.structs = structs
                self.simplyfied_struct_name = simplyfied_struct_name


            def is_variable(self, identifier):
                if identifier in [name for (name, _, _, _) in self.variables] or \
                        identifier in [name for (name, _, _, _) in self.local_variables] or \
                        identifier in [name for (name, _, _, _) in self.parameter_variables]:
                    return True

                return False
            
            def is_lattice_variable(self, identifier):
                return self.succgen.is_lattice_variable(identifier)

        for func_ast in self.global_functions:

                #XXX mostly cp'ed from constructor, move to function or avoid evaluation
                #print "FUNC AST", func_ast
                

                #func_ast.visit()
                rooted_func_ast = pyuppaal.ulp.node.Node('RootNode', func_ast.children)
                funcIdentifierTypeDict = {}
                (_,_,_,funcDict) = func_ast.leaf
                funcIdentifierTypeDict.update(self.pars.globalIdentifierTypeDict)
                funcIdentifierTypeDict.update(funcDict)

                declvisitor = parser.DeclVisitor(FakeParser(rooted_func_ast, self.pars.typedefDict, funcIdentifierTypeDict))
                declvisitor.visit(rooted_func_ast)
                #print "function: ", func_ast.leaf[1].children[0] #, funcIdentifierTypeDict #, funcSimplyfied_struct_name #, self.pars.globalIdentifierTypeDict
                func_constants = {}
                funcSimplyfied_struct_name = dict(self.simplyfied_struct_name)

                #evaluate constants to values
                for (cident, cval) in declvisitor.constants.iteritems():
                    if not cident in func_constants:
                        func_constants[cident] = eval(util.expression_to_python(cval), {}, dict(self.constants.items() + func_constants.items()))
    
                func_variables = []
                #evaluate array dimensions to values
                for vdecl in declvisitor.variables:
                    util.eval_vardecl_expressions(vdecl, 
                        dict(self.constants.items() + func_constants.items()),
                        do_eval_initval=False)
                    func_variables.append(vdecl)

                
                #add function parameter variables
                parameter_variables = [] 
                if len(func_ast.leaf[2]):
                    (_,_,parameters,_) = func_ast.leaf
                    ast = pyuppaal.ulp.node.Node('RootNode', parameters)
                    parameter_declvisitor = parser.DeclVisitor(FakeParser(ast, self.pars.typedefDict, funcIdentifierTypeDict))
                    parameter_declvisitor.visit(ast)
                    for vdecl in parameter_declvisitor.variables:
                        util.eval_vardecl_expressions(vdecl, self.constants, do_eval_initval=False)
                        if util.is_struct_type(vdecl.vartype, self.structs):
                            parameter_variables.extend(util.getStructVarDecl(vdecl, self.structs, self.constants, vdecl.identifier))
                            funcSimplyfied_struct_name[vdecl.identifier] = vdecl.vartype
                        else:
                            parameter_variables.append(vdecl)
                
                func_succgen = FuncSuccGen(self, func_variables, parameter_variables, func_constants, self.structs, funcSimplyfied_struct_name)
                func_succgen.pars.identifierTypeDict = funcIdentifierTypeDict
                constant_decl = self.generateConstants(func_constants)
                (_,par_parts) = util.makeVariableList(parameter_variables, True)
                
                cfunc = util.uppaalcfunc_to_cfunc(func_ast, func_succgen, constant_decl, func_variables, par_parts)
                cfunctions.append(cfunc)
        
        return ''.join(cfunctions)

    def generateInitialState(self):
        parts = ["""static state_struct_t initial_state = {\n""" ]
        # Variables {{{
        for vdecl in self.discrete_variables:
            var = vdecl.identifier; array_dimensions = vdecl.eval_dimensions

            if array_dimensions == []:
                initval = vdecl.eval_initval or "0"

                if vdecl.vartype == "TypeBool":   
                    initval = str(initval).lower()
                parts += ["\t%s, /* %s */\n" % (initval, var)]
            else:
                parts += '\t'
                parts.extend(util.init_array(vdecl.initval,vdecl.eval_dimensions, self.constants))
                parts += ',\n'
        #}}}
        # Locations {{{
        for (idx, t) in enumerate(self.model.templates):
            parts += ["\t%d, /* %s */\n" % (t.locations.index(t.initlocation), t.name)]
        #}}}
        # symbolic lattice part
        if self.usesDBM:
            parts += ["\tNULL, /* fed part */\n"]
        elif len(self.externs):
            assert len(self.lattice_variables) == 1, "XXX multiple lattice vars not supported"
            for lat_obj in self.lattice_variables:
                parts += ["\t" + lat_obj.generateInitialStatePart() + "\n"]
        parts += ["};\n"]
        return "".join(parts)

    def generate_lattice_support_funcs(self):
        if self.usesDBM:
            return """
extern "C" dbm::fed_t* lattice_clone (const dbm::fed_t *fed) {
    return new dbm::fed_t(fed->const_dbmt().const_dbm(), %d);
}

extern "C" int lattice_cmp (const dbm::fed_t *fed1, const dbm::fed_t *fed2) {
    if (fed1 == fed2 || *fed1 == *fed2)
    	return 0; // equal
    return 1;
}

extern "C" uint32_t lattice_hash (const dbm::fed_t *fed) {
    return fed->hash();
}

extern "C" void lattice_delete (const dbm::fed_t *fed) {
    delete fed;
}
""" % (len(self.clocks) + 1)
        elif len(self.externs):
            assert len(self.lattice_variables) == 1, "XXX multiple lattice vars not supported"
            parts = ["""
extern "C" void* lattice_clone (void *a) {
"""]
            for lat_obj in self.lattice_variables:
                parts += ["\treturn " + lat_obj.generateLatticeClonePart("a") + ";\n"]
            parts += ["\n}"]

            parts += ["""
extern "C" int lattice_cmp (const void *a, const void *b) {
    /*
    printf("cmp: %p %p\\n", a, b);
    */
    //printf("env: %p\\n", oct_oct_env);
    //printf("man: %p\\n", oct_oct_man);
    if ("""]
            for lat_obj in self.lattice_variables:
                parts += [lat_obj.generateLatticeCmpPart("a", "b") + "\n"]
            parts += [""")
    	return 0; // equal
    return 1;
}

extern "C" uint32_t lattice_hash (const void *a) {
    return """]
            #XXX how to hash more than one?
            for lat_obj in self.lattice_variables:
                parts += [lat_obj.generateLatticeHashPart("a") + "\n"]
            parts += [""";
    return 42; // XXX, hash for real
}

extern "C" void lattice_delete (const void *a) {
"""]
            for lat_obj in self.lattice_variables:
                parts += [lat_obj.generateLatticeDeletePart("a") + "\n"]
            parts += ["""
}
"""]
            return "".join(parts)
        else:
            return ""

    def generate_label_funcs(self):
        parts = []
        guard_labels = [] #XXX no guard labels
        int_labels = self.chan_label_list.keys()
        string_labels = []

        if self.usesDBM or len(self.externs):
            string_labels += ["lattice"] #the lattice label

        parts += ["""
extern "C" const int opaal_get_guard_count() 
{
    return %d;
}
extern "C" const int opaal_get_string_label_count() 
{
    return %d;
}
extern "C" const int opaal_get_label_count() 
{
    return %d;
}


""" % (len(guard_labels), len(string_labels), 
    len(self.edge_label_list) + len(guard_labels) + len(int_labels) + len(string_labels))]

        parts += ["""
extern "C" const int opaal_get_label(void* model, int g, state_struct_t* src) 
{
    (void)model;
    return false; //no regular labels for now
}
extern "C" void opaal_get_labels_all(void* model, state_struct_t* src, int* guard)
{
    (void)model;
    return; //no regular labels for now
}
"""]
        subparts= []
        #subparts = self.chan_label_list.keys()
        for (i, l) in enumerate(string_labels+ self.edge_label_list+guard_labels +  int_labels):
            subparts += ["        case %d: return \"%s\";" % (i, l)]

        parts += ["""
extern "C" const char* opaal_get_label_name(int g) 
{
    switch (g) {
%s
        default:
            return NULL;
    }
}""" % ("\n".join(subparts))]

        parts += ["""
extern "C" const char* opaal_get_string_label(void* model, int g, state_struct_t* src) 
{
    switch (g) {
"""]
        if self.usesDBM or len(self.externs):
            parts += ["case 0: return lattice_print(lattice_part(src));\n"]
        parts += ["""
        default:
            return NULL;
    }
}

extern "C" void opaal_get_string_labels_all(void* model, state_struct_t* src, const char** labels) 
{
"""]
        if self.usesDBM or len(self.externs):
            parts += ["labels[0] = lattice_print(lattice_part(src));\n"]
        parts += ["""
}
"""]
        return "".join(parts)

    def generate_do_callback(self):
        parts = ["""
void do_callback(state_struct_t *in, state_struct_t *out, transition_info_t *transition_info, void (*callback)(void *arg, transition_info_t *transition_info, state_struct_t *out), void *arg) {
"""]
        #do delay
        if self.usesDBM:
            if self.analyzer.has_clockrates:
                parts += ["\tif (!state_is_urgent(out)) do_stopwatch_delay(out);\n"]
            else:
                parts += ["\tif (!state_is_urgent(out)) out->fed->up();\n"]
        #apply/evaluate invariants
        parts += ["\tif (apply_invariants(out)) {\n"]
        #local extrapolation
        if self.usesDBM:
            parts += ["\t\tdo_extrapolation(out);\n"]
            parts += ["\t\tout->fed->mergeReduce();\n"]
        elif len(self.externs) >= 1:
            for lat_obj in self.lattice_variables:
                parts += [lat_obj.generateCallbackPart("out") + "\n"]

        #callback
        parts+= ["""
\t\tcallback(arg, transition_info, out);
\t}
"""]
        parts += ["}\n"]
        return "".join(parts)

    def generate_get_successors(self):
        parts = ["""
extern "C" int get_successors( void *model, state_struct_t *in, void (*callback)(void *arg, transition_info_t *transition_info, state_struct_t *out), void *arg ) 
{
    (void)model; // ignore model
    bool system_in_deadlock = true;
    transition_info_t transition_info = { NULL, -1 };
    int states_emitted = 0;
    state_struct_t tmp;
    state_struct_t *out = &tmp;

"""]
        for priority_group in reversed(self.priority_groups):
            for t in priority_group:
                t_idx = self.model.templates.index(t)
                parts += self._generate_commited_get_successors_for_template(t_idx, t)
            #end of priority group, early return if we generated states
            parts += ["\tif (states_emitted) return states_emitted;\n"]
        #end of committed transitions, early return if state is committed
        parts += ["\tif (state_is_committed(in)) return states_emitted;\n"]

        for priority_group in reversed(self.priority_groups):
            for t in priority_group:
                t_idx = self.model.templates.index(t)
                parts += self._generate_get_successors_for_template(t_idx, t)
            #end of priority group, early return if we generated states
            parts += ["\tif (states_emitted) return states_emitted;\n"]

        parts += ["\treturn states_emitted;\n};\n"]

        return "".join(parts)

    def _generate_commited_get_successors_for_template(self, t_idx, t):
        parts = ["\t/* Committed transitions for %s {{{*/\n\tswitch( in->%s ) {\n" % (t.name, t.name)]
        had_committed_locs = False
        for (l_idx, l) in enumerate(t.locations):
            if l.committed: 
                had_committed_locs = True
                parts += self._generate_get_successors_for_location(t_idx, t, l_idx, l)
        if not had_committed_locs:
            return []
        parts += ["\t}\n"]
        parts += ["\t/* }}} */\n"]
        return parts

    def _generate_get_successors_for_template(self, t_idx, t):
        parts = ["\t/* Transitions for %s {{{*/\n\tswitch( in->%s ) {\n" % (t.name, t.name)]
        for (l_idx, l) in enumerate(t.locations):
            if not l.committed: 
                parts += self._generate_get_successors_for_location(t_idx, t, l_idx, l)
        parts += ["\t}\n"]
        parts += ["\t/* }}} */\n"]
        return parts

    def _generate_get_successors_for_location(self, t_idx, t, l_idx, l):
        parts = ["\t\tcase %d:" % (l_idx)]
        if l.name.value:
            parts += [" /* %s */\n" % (l.name)]
        else:
            parts += ["\n"]
        for (target_idx, guard_code, update_code, fed_update, (sync, sync_index_exprs), debug_info) in self.transitions[t_idx][l_idx]:
            #print "%s"%(t.locations[target_idx])
            #print "%s"%(t.locations.index(t_idx))
            tname = t.locations[target_idx].name.value
            #If synchronisation, find trans to sync with
            if sync:
                if sync[-1] == '?':
                    #Only look for matching pair to ! syncs
                    continue
                #Evaluate guard
                parts += ["\t\t\tif( %s ) {\n" % (guard_code)]

                chan_name = sync[:-1]
                brother_sync = chan_name + '?'
                
                #edge_label = "%s_%s_%s" %(l.name.value, chan_name, tname)
                #print edge_label
                #self.edge_label_list.append(edge_label);

                #2-Way handshake
                if chan_name in self.channels + self.urgent_channels:
                    edge_label = "%s_%s_%s" %(l.name.value, chan_name, tname)
                    self.edge_label_list.append(edge_label);
                    label_idx = len(self.edge_label_list);
                    print edge_label

                    parts += self._generate_receivers_for_2way_sync(t_idx, t, chan_name, sync_index_exprs, target_idx, fed_update, update_code,label_idx)
                elif chan_name in self.broadcast_channels + self.urgent_broadcast_channels: #broadcast sync
                    edge_label = "%s_%s_%s" %(l.name.value, chan_name, tname)
                    self.edge_label_list.append(edge_label);
                    label_idx = len(self.edge_label_list);
                    print edge_label
                    parts += ["\t\t\t\t/* sender side of broadcast sync on %s */\n" % (chan_name)]
                    parts += ["\t\t\t\t*out = *in;\n"]
                    if self.usesDBM:
                        parts += ["\t\t\t\tassert(in->fed->size() == 1);\n"]
                        parts += ["\t\t\t\tdbm::fed_t outfed(in->fed->const_dbmt().const_dbm(), %d);\n" % (len(self.clocks) + 1)]
                        parts += ["\t\t\t\tout->fed = &outfed;\n"]
                        parts += ["\t\t\t\t\t\t\t%s\n" % (fed_update)]
                        parts += ["\t\t\t\tif (!(out->fed->isEmpty())) {\n"]
                    #move location
                    parts += ["\t\t\t\tout->%s = %d;\n" % (t.name, target_idx)]
                    #do updates
                    parts += ["\t\t\t\t%s\n" % (update_code)]

                    for (t2_idx, t2) in enumerate(self.model.templates):
                        syncs_between_these_templates = False
                        subparts = []
                        #the two synchronizers should be different
                        if t_idx == t2_idx:
                            continue
                        subparts += ["\t\t\t\t/* bcast receiver Syncs with %s on %s {{{*/\n\t\t\t\tswitch( in->%s ) {\n" % (t2.name, chan_name, t2.name)]
                        for (l2_idx, l2) in enumerate(t2.locations):
                            thislocpart = ["\t\t\t\t\tcase %d:" % (l2_idx)]
                            syncs_between_these_locations = False
                            if l2.name.value:
                                thislocpart += [" /* %s */\n" % (l2.name)]
                            else:
                                thislocpart += ["\n"]
                            for (target2_idx, guard_code2, update_code2, fed_update2, (sync2, index_exprs2), debug_info2) in self.sync_transitions[t2_idx][l2_idx][brother_sync]:
                                syncs_between_these_templates = True
                                syncs_between_these_locations = True
                                #Evaluate guard2
                                thislocpart += ["\t\t\t\t\t\tif( %s ) {\n" % (guard_code2)]
                                assert fed_update2 == "/* nop */", "Clock guards not allowed on broadcast receivers"
                                #move location
                                thislocpart += ["\t\t\t\t\t\t\tout->%s = %d;\n" % (t2.name, target2_idx)]
                                #do update
                                thislocpart += ["\t\t\t\t\t\t\t%s\n" % (update_code2)]

                                thislocpart += ["\t\t\t\t\t\t}\n"]
                            thislocpart += ["\t\t\t\t\tbreak;\n"]
                            if syncs_between_these_locations:
                                subparts += thislocpart
                        subparts += ["\t\t\t\t}\n"]
                        subparts += ["\t\t\t\t/* }}} */\n"]
                        if syncs_between_these_templates:
                            parts += subparts
                    #callback
                    parts += ["""
        system_in_deadlock = false;
        int label_list[] = {%d, 0};
        transition_info.label = label_list;
        transition_info.group = -1;
        do_callback(in, out, &transition_info, callback, arg);
        ++states_emitted;
"""%(label_idx)]
                    if self.usesDBM:
                        parts += ["\t\t\t\t}\n"]
                else:
                    assert False, "channel '%s' not found" % chan_name
                parts += ["\t\t\t}\n"]

            else: #ordinary transition
                #Evaluate discrete guard
                parts += ["\t\t\tif( %s ) {\n" % (guard_code)]
                parts += ["\t\t\t\t*out = *in;\n"]
                
                edge_label = "%s_%s" %(l.name.value, tname)
                print edge_label
                self.edge_label_list.append(edge_label);
                label_idx = len(self.edge_label_list)
                text = "label: %s" %(edge_label)
                print text


                if self.usesDBM:
                    parts += ["\t\t\t\tassert(in->fed->size() == 1);\n"]
                    parts += ["\t\t\t\tdbm::fed_t outfed(in->fed->const_dbmt().const_dbm(), %d);\n" % (len(self.clocks) + 1)]
                    parts += ["\t\t\t\tout->fed = &outfed;\n"]
                    parts += ["\t\t\t\t%s\n" % (fed_update)]
                    parts += ["\t\t\t\tif (!(out->fed->isEmpty())) {\n"]
                elif self.externs:
                    assert len(self.lattice_variables) == 1, "XXX multiple lattice vars not supported"
                    for lat_obj in self.lattice_variables:
                        parts += ["\t\t\t\t" + lat_obj.generateCopyPart("in", "out") + "\n"]

                #parts += ["""printf("in->fed = %p\\n", in->fed); printf("out->fed = %p\\n", out->fed);\n"""]
                #move location
                parts += ["\t\t\t\tout->%s = %d;\n" % (t.name, target_idx)]
                #do discrete update
                parts += ["\t\t\t\t%s\n" % (update_code)]

                #callback
                parts += ["""
            system_in_deadlock = false;
            int label_list[] = {%d, 0};
            transition_info.label = label_list;
            transition_info.group = -1;
            do_callback(in, out, &transition_info, callback, arg);
            ++states_emitted;
"""%(label_idx)]

                if self.usesDBM:
                    parts += ["\t\t\t\t}\n"]
                    #parts += ["\t\t\t\telse delete out->fed;\n"]

                parts += ["""
        }
"""]
        parts += ["\t\tbreak;\n"]
        return parts

    def _generate_receivers_for_2way_sync(self, t_idx, t, chan_name, chan_array_index_exprs, target_idx, fed_update, update_code, 
    label_idx, mother_chan_name=None, remaining_dimensions=None):
        parts = []
        mother_chan_name = mother_chan_name or chan_name
        if remaining_dimensions is None and chan_array_index_exprs: #we don't know the dimensions, and we need to
            logger.debug("dimensions for '%s':", mother_chan_name)
            remaining_dimensions = ([d for (i,d) in self.declvisitor.channels if i == mother_chan_name] +
                [d for (i,d) in self.declvisitor.urgent_channels if i == mother_chan_name])[0]
            logger.debug("%s", remaining_dimensions)
        else:
            remaining_dimensions = []
        assert len(remaining_dimensions) == len(chan_array_index_exprs), "%s %s" % (remaining_dimensions, chan_array_index_exprs)
        
        if chan_array_index_exprs == []: #chan_name fully determined
            brother_sync = chan_name + '?'
            for (t2_idx, t2) in enumerate(self.model.templates):
                syncs_between_these_templates = False
                subparts = []
                #the two synchronizers should be different
                if t_idx == t2_idx:
                    continue
                subparts += ["\t\t\t\t/* Syncsf with %s on %s {{{*/\n\t\t\t\tswitch( in->%s ) {\n" % (t2.name, chan_name, t2.name)]
                for (l2_idx, l2) in enumerate(t2.locations):
                    thislocpart = ["\t\t\t\t\tcase %d:" % (l2_idx)]
                    syncs_between_these_locations = False
                    if l2.name.value:
                        thislocpart += [" /* %s */\n" % (l2.name)]
                    else:
                        thislocpart += ["\n"]
                    for (target2_idx, guard_code2, update_code2, fed_update2, (sync2, index_exprs2), debug_info2) in self.sync_transitions[t2_idx][l2_idx][brother_sync]:
                        #XXX dynamic sync receivers not supported!
                        assert index_exprs2 == []
                        syncs_between_these_templates = True
                        syncs_between_these_locations = True
                        thislocpart += self._generate_2way_sync_receiver(t_idx, t, t2_idx, t2, target_idx, target2_idx, guard_code2, fed_update, fed_update2, update_code, update_code2, chan_name, label_idx)
                    thislocpart += ["\t\t\t\t\tbreak;\n"]
                    if syncs_between_these_locations:
                        subparts += thislocpart
                subparts += ["\t\t\t\t}\n"]
                subparts += ["\t\t\t\t/* }}} */\n"]
                if syncs_between_these_templates:
                    parts += subparts
        else: #chan_name not fully determined
            #Do a switch for this level, with a recursive call
            index_expr = chan_array_index_exprs[0]
            this_dimension = remaining_dimensions[0]
            parts += ["\t\t\t\t/* Syncs on %s {{{*/\n\t\t\t\tswitch( %s ) {\n" % (chan_name , index_expr)]
            for i in range(this_dimension):
                parts += ["\t\t\t\t\tcase %d: /* %s */\n" % (i, chan_name + "[%d]" % (i))]
                parts += self._generate_receivers_for_2way_sync(t_idx, t, 
                        chan_name + "[%d]" % (i), chan_array_index_exprs[1:], 
                        target_idx, fed_update, update_code, label_idx, mother_chan_name, 
                        remaining_dimensions[1:])
                parts += ["\t\t\t\t\tbreak;\n"]
            
            parts += ["\t\t\t\t\tdefault:\n"]
            parts += ["\t\t\t\t\t\tassert(false);\n"]
            parts += ["\t\t\t\t\tbreak;\n"]
            parts += ["\t\t\t\t}\n"]
            parts += ["\t\t\t\t/* }}} */\n"]
        return parts

    def _generate_2way_sync_receiver(self, t_idx, t, t2_idx, t2, target_idx, target2_idx, guard_code2, fed_update, fed_update2, update_code, update_code2, chan_name,label_idx):
        thislocpart = []
        #Evaluate guard2
        thislocpart += ["\t\t\t\t\t\tif( %s ) {\n" % (guard_code2)]
        thislocpart += ["\t\t\t\t\t\t\t*out = *in;\n"]
        if self.usesDBM:
            thislocpart += ["\t\t\t\t\t\t\tassert(in->fed->size() == 1);\n"]
            #thislocpart += ["\t\t\t\t\t\t\tout->fed = new dbm::fed_t(in->fed->const_dbmt().const_dbm(), %d);\n" % (len(self.clocks) + 1)]
            thislocpart += ["\t\t\t\t\t\t\tdbm::fed_t outfed(in->fed->const_dbmt().const_dbm(), %d);\n" % (len(self.clocks) + 1)]
            thislocpart += ["\t\t\t\t\t\t\tout->fed = &outfed;\n"]
            thislocpart += ["\t\t\t\t\t\t\t%s ; %s\n" % (fed_update, fed_update2)]
            thislocpart += ["\t\t\t\t\t\t\tif (!(out->fed->isEmpty())) {\n"]
        #move locations
        thislocpart += ["\t\t\t\t\t\t\tout->%s = %d;\n" % (t.name, target_idx)]
        thislocpart += ["\t\t\t\t\t\t\tout->%s = %d;\n" % (t2.name, target2_idx)]
        #do updates
        thislocpart += ["\t\t\t\t\t\t\t%s\n" % (update_code)]
        thislocpart += ["\t\t\t\t\t\t\t%s\n" % (update_code2)]
        #check for label id
        if chan_name not in self.chan_label_list:
           self.chan_counter += 1
           self.chan_label_list[chan_name] = self.chan_counter
           print(self.chan_label_list)
        chan_id = self.chan_label_list[chan_name]
                            
        #callback
        thislocpart += ["""
\t\t\t\t\t\t\tsystem_in_deadlock = false;
\t\t\t\t\t\t\t//todo: add label
\t\t\t\t\t\t\tint label_list[] = {%d, 0};
\t\t\t\t\t\t\ttransition_info.label = label_list;
\t\t\t\t\t\t\ttransition_info.group = -1;
\t\t\t\t\t\t\tdo_callback(in, out, &transition_info, callback, arg);
\t\t\t\t\t\t\t++states_emitted;
""" % (label_idx)]
        if self.usesDBM:
            thislocpart += ["\t\t\t\t\t\t\t}\n"]
            #thislocpart += ["\t\t\t\telse delete out->fed;\n"]
        thislocpart += ["\t\t\t\t\t\t}\n"]
        return thislocpart

    def generateInitialFuncs(self):
        parts = ["""
extern "C" int get_state_size() {
    return state_size;
}

extern "C" void get_initial_state( void *to )
{
    state_struct_t toret = initial_state;
"""]
        if self.usesDBM:
            #parts += ["\tdbm::fed_t locfed (%d);\n" % (len(self.clocks) + 1)]
            parts += ["\ttoret.fed = new dbm::fed_t(%d);\n" % (len(self.clocks) + 1)]
            #parts += ["\ttoret.fed = &locfed;\n"]
            parts += ["\ttoret.fed->setZero();\n"]
            if self.analyzer.has_clockrates:
                parts += ["\tif (!state_is_urgent(&toret)) do_stopwatch_delay(&toret);\n"]
            else:
                parts += ["\tif (!state_is_urgent(&toret)) toret.fed->up();\n"]
            #parts += ["\tprintf(\"abemad: %p %d\\n\", initial_state.fed, state_size);"]
            #parts += ["\tstd::cout << \"abemad2: \" << initial_state.fed->toString(clockNames) << std::endl;"]
        elif len(self.externs):
            assert len(self.lattice_variables) == 1, "XXX multiple lattice vars not supported"
            for lat_obj in self.lattice_variables:
                parts += ["\t" + lat_obj.generateInitialFuncPart("toret") + "\n"]

        parts += ["\tassert(apply_invariants(&toret));\n"]
        if self.usesDBM:
            parts += ["\tdo_extrapolation(&toret);\n"]

        parts += ["""
    memcpy(to, &toret, state_size);
}

extern "C" int have_property()
{
    return false;
}
"""]
        
        return "".join(parts)

    def generate_apply_invariants(self):
        parts = ["""/* Invariants function {{{ */
inline bool apply_invariants (state_struct_t *out) {
"""]
        for (t_idx, t) in enumerate(self.model.templates):
            template_has_invariants = False
            subparts = ["\t/* Invariants for %s {{{*/\n\tswitch( out->%s ) {\n" % (t.name, t.name)]
            for (l_idx, l) in enumerate(t.locations):
                subparts += ["\t\tcase %d:" % (l_idx)]
                if l.name.value:
                    subparts += [" /* %s */\n" % (l.name)]
                else:
                    subparts += ["\n"]
                (statements, invariant_expression) = self.invariants[t_idx][l_idx]

                if statements:
                    template_has_invariants = True
                    subparts += ["\t\t\t%s\n" % (statements)]
                if invariant_expression:
                    template_has_invariants = True
                    subparts += ["\t\t\tif (!(%s)) return false;\n" % (invariant_expression)]
                subparts += ["\t\tbreak;\n"]
            subparts += ["\t}\n"]
            if template_has_invariants:
                parts += subparts

        if self.usesDBM:
            parts += ["\tif (out->fed->isEmpty()) return false;\n"]
        elif len(self.externs) >= 1:
            for lat_obj in self.lattice_variables:
                parts += [lat_obj.generateApplyInvariantPart("out")]
        parts += ["\treturn true;\n}\n/* }}} */\n"]
        return "".join(parts)

    def generate_committed_bitsets(self):
        parts = ["/* Committed locations bitsets {{{ */\n"]
        for (t_idx, t) in enumerate(self.model.templates):
            parts += ["const std::bitset<%d> %s_committed(std::string(\"" % \
                    (len(t.locations), t.name)]
            for (l_idx, l) in enumerate(reversed(t.locations)):
                if l.committed:
                    parts += ["1"]
                else:
                    parts += ["0"]
            parts += ["\"));\n"]

        parts += ["""
bool state_is_committed (state_struct_t *out) {
    return """]
        subparts = []
        for (t_idx, t) in enumerate(self.model.templates):
            subparts += ["(%s_committed[out->%s])" % (t.name, t.name)]
        parts += [" || ".join(subparts)]
    
        parts += [";\n}\n"]
        parts += ["/* }}} */\n"]
        return "".join(parts)

    def generate_urgent_bitsets(self):
        parts = ["/* Urgent locations bitsets {{{ */\n"]
        for (t_idx, t) in enumerate(self.model.templates):
            parts += ["const std::bitset<%d> %s_urgent(std::string(\"" % \
                    (len(t.locations), t.name)]
            for (l_idx, l) in enumerate(reversed(t.locations)):
                if l.urgent or l.committed:
                    parts += ["1"]
                else:
                    parts += ["0"]
            parts += ["\"));\n"]
        parts += ["""
extern "C" bool state_is_urgent (state_struct_t *out) {
    return """]
        subparts = []
        for (t_idx, t) in enumerate(self.model.templates):
            subparts += ["(%s_urgent[out->%s])" % (t.name, t.name)]
        parts += ["\n\t\t|| ".join(subparts)]
    
        parts += ["\n\t\t|| (state_has_outgoing_enabled_urgent_sync(out));\n}\n"]
        parts += ["/* }}} */\n"]
        return "".join(parts)

    def generate_state_has_outgoing_enabled_urgent_sync(self):
        parts = ["/* State has outgoing enabled urgent sync {{{ */"]
        parts += ["""
extern "C" bool state_has_outgoing_enabled_urgent_sync(state_struct_t *in) {
"""]
        for (t_idx, t) in enumerate(self.model.templates):
            template_has_urgent_syncs = False
            subparts = ["\t/* Checks for %s {{{*/\n\tswitch( in->%s ) {\n" % (t.name, t.name)]
            for (l_idx, l) in enumerate(t.locations):
                location_has_urgent_syncs = False
                location_parts = ["\t\tcase %d:" % (l_idx)]
                if l.name.value:
                    location_parts += [" /* %s */\n" % (l.name)]
                else:
                    location_parts += ["\n"]
                for (target_idx, guard_code, update_code, fed_update, (sync, index_exprs), debug_info) in self.transitions[t_idx][l_idx]:
                    #is sync and is urgent broadcast chan we do not need a partner to be urgent
                    #XXX, if using variables in chan name
                    if sync and sync[-1] == '!' and sync[:-1] in self.urgent_broadcast_channels:
                        location_has_urgent_syncs = True
                        template_has_urgent_syncs = True
                        #Evaluate guard
                        location_parts += ["\t\t\tif( %s ) return true;\n" % (guard_code)]
                    #is sync and is urgent broadcast chan
                    elif sync and sync[-1] == '!' and sync[:-1] in self.urgent_channels:
                        location_has_urgent_syncs = True
                        template_has_urgent_syncs = True
                        brother_sync = sync[:-1] + '?'
                        #Evaluate guard
                        location_parts += ["\t\t\tif( %s ) {\n" % (guard_code)]
                        #XXX look for sync partner
                        for (t2_idx, t2) in enumerate(self.model.templates):
                            syncs_between_these_templates = True
                            syncsubparts = []
                            #the two synchronizers should be different
                            if t_idx == t2_idx:
                                continue
                            syncsubparts += ["\t\t\t\t/* Possible syncs with %s {{{*/\n\t\t\t\tswitch( in->%s ) {\n" % (t2.name, t2.name)]
                            for (l2_idx, l2) in enumerate(t2.locations):
                                thislocpart = ["\t\t\t\t\tcase %d:" % (l2_idx)]
                                syncs_between_these_locations = False
                                if l2.name.value:
                                    thislocpart += [" /* %s */\n" % (l2.name)]
                                else:
                                    thislocpart += ["\n"]
                                for (target2_idx, guard_code2, update_code2, fed_update2, (sync2, index_exprs2), debug_info2) in self.sync_transitions[t2_idx][l2_idx][brother_sync]:
                                    #XXX dynamic sync receivers not supported!
                                    assert index_exprs2 == []
                                    assert fed_update2 == "/* nop */" or fed_update2 == "", "Clock guards on urgent chan receivers not allowed!"
                                    syncs_between_these_templates = True
                                    syncs_between_these_locations = True

                                    thislocpart += ["\t\t\t\t\t\tif( %s ) return true;\n" % (guard_code2)]

                                thislocpart += ["\t\t\t\t\tbreak;\n"]
                                if syncs_between_these_locations:
                                    syncsubparts += thislocpart
                            syncsubparts += ["\t\t\t\t}\n"]
                            syncsubparts += ["\t\t\t\t/* }}} */\n"]
                            if syncs_between_these_templates:
                                location_parts += syncsubparts
                        location_parts += ["\t\t\t}\n"]
                if location_has_urgent_syncs:
                    subparts += location_parts
            subparts += ["\t} /* }}} */\n"]
            if template_has_urgent_syncs:
                parts += subparts
        parts += ["\treturn false;\n}\n"]
        return "".join(parts)


    def generate_extrapolate_max_constants(self):
        """
        Code for k-extrapolation. Only for comparison purposes. 
        You should probably use LU-extrapolation instead.
        """
        if not self.usesDBM:
            return ""

        parts = ["/* Max clock constants {{{ */\n"]
        #generate subtable for each template
        for (t_idx, t) in enumerate(self.model.templates):
            parts += ["""const int max_constants_%s[%d][%d] = {
""" % (t.name, len(t.locations), len(self.clocks)+1)]
            for (l_idx, l) in enumerate(t.locations):
                l_maxconstvec = self.analyzer.max_constants[t_idx][l_idx]
                
                parts += ["\t{"]
                for (c_idx, c) in enumerate(self.clock_indexes):
                    if c_idx == 0: # 0clock
                        parts += ["-dbm_INFINITY,"]
                    elif l_maxconstvec[c] == -1:
                        parts += ["-dbm_INFINITY,"]
                    else:
                        parts += ["%d," % l_maxconstvec[c]]
                parts += ["},\n"]
            parts += ["};\n"]


        parts += ["""
#define max( a, b ) ( ((a) > (b)) ? (a) : (b) )
inline void do_extrapolation (state_struct_t *out) {
	int local_max_consts[%d] = {0, %s};
	int i;
""" % (len(self.clocks) + 1, "-dbm_INFINITY, " * (len(self.clocks)))] 

        parts += ["\tfor (i = 0; i < %d; i++) {\n" % (len(self.clocks) + 1)]
        for (t_idx, t) in enumerate(self.model.templates):
            parts += ["\t\tlocal_max_consts[i] = max( local_max_consts[i], max_constants_%s[out->%s][i] );\n" % 
                    (t.name, t.name)]

        parts += ["\t}\n"]

        parts += ["""
    out->fed->extrapolateMaxBounds(local_max_consts);
}\n"""]

        parts += ["/* }}} */\n"]
        return "".join(parts)

    def generate_extrapolate_lu_bounds(self):
        """
        Lower-Upper bound extrapolation.
        """
        if not self.usesDBM:
            return ""

        parts = ["/* Lower/Upper clock bounds {{{ */\n"]
        lowerparts = []
        upperparts = []
        #generate subtable for each template
        for (t_idx, t) in enumerate(self.model.templates):
            lowerparts += ["""const int clock_lower_bounds_%s[%d][%d] = {
""" % (t.name, len(t.locations), len(self.clocks)+1)]
            upperparts += ["""const int clock_upper_bounds_%s[%d][%d] = {
""" % (t.name, len(t.locations), len(self.clocks)+1)]

            for (l_idx, l) in enumerate(t.locations):
                l_lowerboundvec = self.analyzer.lowerbound[t_idx][l_idx]
                l_upperboundvec = self.analyzer.upperbound[t_idx][l_idx]
                
                lowerparts += ["\t{"]
                upperparts += ["\t{"]
                for (c_idx, c) in enumerate(self.clock_indexes):
                    if c_idx == 0: # 0clock
                        lowerparts += ["-dbm_INFINITY,"]
                        upperparts += ["-dbm_INFINITY,"]
                    else:
                        if l_lowerboundvec[c] == -1:
                            lowerparts += ["-dbm_INFINITY,"]
                        else:
                            lowerparts += ["%d," % l_lowerboundvec[c]]
                        if l_upperboundvec[c] == -1:
                            upperparts += ["-dbm_INFINITY,"]
                        else:
                            upperparts += ["%d," % l_upperboundvec[c]]
                lowerparts += ["},\n"]
                upperparts += ["},\n"]
            lowerparts += ["};\n"]
            upperparts += ["};\n"]

        parts += lowerparts
        parts += upperparts

        parts += ["""
#define max( a, b ) ( ((a) > (b)) ? (a) : (b) )
inline void do_extrapolation (state_struct_t *out) {
	int local_lower_bounds[%d] = {0, %s};
	int local_upper_bounds[%d] = {0, %s};
	int i;
""" % (len(self.clocks) + 1, "-dbm_INFINITY, " * (len(self.clocks)),
       len(self.clocks) + 1, "-dbm_INFINITY, " * (len(self.clocks)))] 

        parts += ["\tfor (i = 0; i < %d; i++) {\n" % (len(self.clocks) + 1)]
        for (t_idx, t) in enumerate(self.model.templates):
            parts += ["\t\tlocal_lower_bounds[i] = max( local_lower_bounds[i], clock_lower_bounds_%s[out->%s][i] );\n" % 
                    (t.name, t.name)]
            parts += ["\t\tlocal_upper_bounds[i] = max( local_upper_bounds[i], clock_upper_bounds_%s[out->%s][i] );\n" % 
                    (t.name, t.name)]

        parts += ["\t}\n"]

        #The most coarse extrapolation from
        #"Lower and Upper Bounds in Zone Based Abstractions of Timed Automata" by 
        #Gerd Behrmann, Patricia Bouyer, Kim G. Larsen and Radek Pelanek
        parts += ["""
    out->fed->diagonalExtrapolateLUBounds(local_lower_bounds, local_upper_bounds);
}\n"""]

        parts += ["/* }}} */\n"]
        return "".join(parts)


    def generate_clock_rates(self):
        if not self.usesDBM or not self.analyzer.has_clockrates:
            return ""
        parts = ["/* Clock rates / stopwatches {{{ */\n"]
        #generate subtable for each template
        for (t_idx, t) in enumerate(self.model.templates):
            parts += ["const std::bitset<%d> clock_rates_%s[%d] {\n" % \
                    (len(self.clocks)+1, t.name, len(t.locations))]
            for (l_idx, l) in enumerate(reversed(t.locations)):
                parts += ["\tstd::bitset<%d>(std::string(\"" % (len(self.clocks)+1)]
                l_clockratevec = self.analyzer.clockrates[t_idx][l_idx]
                subparts = []
                for (c_idx, c) in enumerate(self.clock_indexes):
                    if c_idx == 0: # 0clock
                        subparts += ["1"]
                    else:
                        subparts += ["%d" % l_clockratevec[c]]
                #indexes should be in "reverse" order
                parts += ["".join(subparts[::-1])]
                parts += ["\")),\n"]
            parts += ["};\n"]

        parts += ["""
void do_stopwatch_delay(state_struct_t *out) {
    std::bitset<%d> clockrates(std::string("%s"));
""" % (len(self.clocks) + 1, "1" * (len(self.clocks)+1))] 

        for (t_idx, t) in enumerate(self.model.templates):
            parts += ["\tclockrates &= clock_rates_%s[out->%s];\n" % 
                    (t.name, t.name)]
        numclocks = len(self.clocks)+1
        parts += ["""
	uint32_t asbits[%d] = {%s};
	for (int i = 0; i < %d; i++) {
		if (clockrates[i]) /* clear the bit if rate is 1 (not stopped) */
			asbits[i >> 5] &= ~(1 << (i & 31));
		else /* set the bit if rate is 0 (stopped) */
			asbits[i >> 5] |= 1 << (i & 31);
	}
	out->fed->upStop(asbits);
}\n""" % ( numclocks/32+1, "0,"*(numclocks/32+1), numclocks)]
        parts += ["/* }}} */\n"]

        return "".join(parts)

    def generateStubs(self):
        parts = ["""
 
extern "C" int get_successor( void* model, int t, state_struct_t *in, void (*callback)(void* arg, transition_info_t *transition_info, state_struct_t *out), void *arg ) 
{
    return 0;
}
"""]
        #XXX, this is stubby
        parts += ["""
int transition_dependency[%d] = { %s };

extern "C" const int* get_transition_read_dependencies(int t) 
{
    return transition_dependency;
}
extern "C" const int* get_transition_write_dependencies(int t) 
{
    return transition_dependency;
}
""" % (self.getFieldsSize(self.StateStruct._fields_), "1," * self.getFieldsSize(self.StateStruct._fields_))]

        #XXX, this is stubby
        parts += ["""
extern "C" const int get_guard_count() 
{
    return 0;
}
extern "C" const int* get_guard_matrix(int g) 
{
    return NULL;
}
extern "C" const int* get_guards(int t) 
{
    return NULL;
}
extern "C" const int** get_all_guards() 
{
    return NULL;
}
extern "C" int get_guard(void* model, int g, state_struct_t* src) 
{
    return 0;
}
extern "C" void get_guard_all(void* model, state_struct_t* src, int* guard) 
{
}
extern "C" const int* get_guard_may_be_coenabled_matrix(int g) 
{
    return NULL;
}
extern "C" const int* get_guard_nes_matrix(int g) 
{
    return NULL;
}
extern "C" const int* get_guard_nds_matrix(int g) 
{
    return NULL;
}
"""]


        return "".join(parts)


    def generateCoverFunction(self):
        #TODO: covered_by_short should/could be changed to take two void*,
        #if LTSmin is changed accordingly
        if self.usesDBM:
            return """
typedef union fed_u {
   dbm::fed_t  *fed;
   uint64_t    fill;
} fed_u_t;

extern "C" int covered_by_short( int *fed_a, int *fed_b) 
{
    fed_u_t pa = *((fed_u_t*)fed_a);
    fed_u_t pb = *((fed_u_t*)fed_b);

    /*std::cout << "cover: " << 
	    pa.fed->toString(clockNames) << 
	    " " << 
	    pb.fed->toString(clockNames) << std::endl;*/

    if ( *(pa.fed) <= *(pb.fed) )
	return 1;
    else
        return 0;
}"""
        elif len(self.externs):
            parts = ["""
extern "C" int covered_by_short( void **a, void **b)
{
    /*
    lattice_print(*(ap_abstract1_t**)a);
    lattice_print(*(ap_abstract1_t**)b);
    printf("%p %p ", a, b);
    */
    if ("""]
            assert len(self.lattice_variables) == 1, "XXX multiple lattice vars not supported"
            for lat_obj in self.lattice_variables:
                parts += [lat_obj.generateCoverPart("a", "b") + "\n"]
            
            parts += [""") {
        /*
        printf("covered\\n");
        */
    	return 1;
    }
    else {
        /*
        printf("not\\n");
        */
        return 0;
    }
}

extern "C" int covered_by( state_struct_t *a, state_struct_t *b) 
{
    void *la = lattice_part(a);
    void *lb = lattice_part(b);
    return covered_by_short(&la, &lb);
}
"""]
            return "".join(parts)
        else:
            return 'extern "C" int covered_by_short( int *fed_a, int *fed_b) { return 1; }'

    def generateJoinFunction(self):
        if len(self.externs):
            parts = ["""
extern "C" int join_with_short( void *a, void *b)
{
    """]
            assert len(self.lattice_variables) == 1, "XXX multiple lattice vars not supported"
            for lat_obj in self.lattice_variables:
                parts += [lat_obj.generateJoinPart("a", "b") + "\n"]
            parts += ["""
}

extern "C" int join_with ( state_struct_t *a, state_struct_t *b) 
{
    return join_with_short(lattice_part(a), lattice_part(b));
}
"""]
            return "".join(parts)
        else:
            return """
extern "C" void join_with_short( void *a, void *b) { return; }
extern "C" void join_with ( state_struct_t *a, state_struct_t *b) { return; }
"""



    def is_variable(self, identifier):
        if identifier in [name for (name, _) in self.clocks]:
            return False

        if identifier in [name for (name, _, _, _) in self.variables]:
            return True
        return False

    def get_lattice_variable(self, identifier):
        for lat_obj in self.lattice_variables:
            if lat_obj.name == identifier:
                return lat_obj
        return None

    def is_lattice_variable(self, identifier):
        if self.get_lattice_variable(identifier):
            return True
        return False

    #}}}
    #{{{ opaal interface to object file
    def _get_object_file(self):
        if not self.ofilelib:                        
            cfile = tempfile.NamedTemporaryFile(suffix='.cpp')
            cfilename = cfile.name
            #To DEBUG: comment in the next two lines
            #cfilename = "/tmp/gensuccgen.cpp"
            #cfile = open(cfilename, 'w')
            
            # use (unique) temporary filename, otherwise loadlibrary will cache the call
            ofile = tempfile.NamedTemporaryFile()
            ofilename = ofile.name
            #ofilename = "/tmp/gensuccgen.so"

            self.generateCFile(cfile)
            cfile.flush()

            if len(self.externs) >= 1:
                ldflags = ""
                for (_, cls) in self.externs.iteritems():
                    ldflags += cls.getCompilerLinkFlags()
                os.system("g++ -g -O0 -fPIC -shared -o %s %s %s" % (ofilename, cfilename, ldflags))
            else:
                #assume DBMs by default
                #figure out where the UPPAAL DBM library is installed
                #try with udbm-config binary
                try:
                    uppaal_dbm_include_dir = subprocess.check_output(["udbm-config", "--inc"]).split()[0]
                    uppaal_dbm_lib_dir = subprocess.check_output(["udbm-config", "--libs"]).split()[0] #only need dir
                except:
                    if os.path.exists("../usr/uppaal/"):
                        uppaal_dbm_include_dir = "-I../usr/uppaal/include/"
                        uppaal_dbm_lib_dir = "-L../usr/uppaal/lib/"
                    else:
                        uppaal_dbm_include_dir = "-I/usr/local/uppaal/include/"
                        uppaal_dbm_lib_dir = "-L/usr/local/uppaal/lib/"
               
                execStr = "g++ -g -O0 -fPIC -shared %s %s -o %s %s -Wno-int-to-pointer-cast -ludbm" % \
                            (uppaal_dbm_include_dir, uppaal_dbm_lib_dir, ofilename, cfilename)

                try:
                    output = subprocess.check_output(execStr, stderr=subprocess.STDOUT, shell=True)
                except subprocess.CalledProcessError, e:
                    print "Stdout:\n", e.output 
                    cfile.seek(0)
                    print cfile.read()

            cfile.close()
            self.ofilelib = cdll.LoadLibrary(ofilename)

        return self.ofilelib

    def get_initialstate(self):
        object_file = self._get_object_file()
        s1 = self.StateStruct()
        object_file.get_initial_state(pointer(s1))
        init_state = copy.copy(s1)
        return init_state

    def successors(self, state, trans_info=False):
        object_file = self._get_object_file()
        self._temp_succs = []
        object_file.get_successors(None, pointer(state), 
                self.cbfunc(self._get_successors_cb),
                None)
        logger.debug("returning %s", self._temp_succs)
        return self._temp_succs

    def _get_successors_cb(self, arg, trans_info, out):
        
        succ = copy.copy(out.contents)
        self._temp_succs += [succ]

    def _covered_by_short(self, state, other):
        logger.debug("_covered_by_short: %s %s ?", state, other)
        object_file = self._get_object_file()
        size = object_file.get_state_size()

        return object_file.covered_by_short(
                byref(state, size-sizeof(POINTER(c_uint))),                
                byref(other, size-sizeof(POINTER(c_uint))))

    #}}}



if __name__ == '__main__':
    import sys
    file = open(sys.argv[1])
    nta = pyuppaal.NTA.from_xml(file)
    outfile = open(sys.argv[2], 'w')

    if False:
        import cProfile
        cProfile.run('s = GenerateSuccessorGenerator(nta)', '/tmp/opaal_prof%d.txt' % (1))
        cProfile.run('s.generateCFile(outfile)', '/tmp/opaal_prof%d.txt' % (2))
    else:
        s = GenerateSuccessorGenerator(nta)
        s.generateCFile(outfile)
# vim:ts=4:sw=4:expandtab
