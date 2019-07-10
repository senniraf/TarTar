#!/usr/bin/python
# -*- coding: utf-8 -*-
### BEGIN LICENSE
# Copyright (C) 2010 Mads Chr. Olesen <mchro@cs.aau.dk>
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
import copy
import re
import numpy
import sys
import logging
from functools import partial
logger = logging.getLogger('pyuppaal.analyzer')

import pyuppaal
from pyuppaal.ulp import lexer, parser, expressionParser, updateStatementParser

import util
import opaal.util

class AnalyzeModel:
    """Do various analyses on a pyuppaal model"""

    def __init__(self, nta, constant_overrides=dict()):
        self.nta = nta
        self.constant_overrides = constant_overrides
        self.parse_and_calculate_constants()
        #XXX, also include lattice vars inheriting from TimeLattice
        self._clocks = map(lambda (x,y): x, self.declvisitor.clocks)
        self.live_clocks = {}
        self.max_constants = {}
        self.upperbound = {}
        self.lowerbound = {}
        self.has_clockrates = False
        self.clockrates = {}
        self.live_variables = {}
        self.location_has_clockrates = {}
        for t_idx, t in enumerate(self.nta.templates):
            self.max_constants[t_idx] = {}
            self.upperbound[t_idx] = {}
            self.lowerbound[t_idx] = {}
            self.clockrates[t_idx] = {}
            self.live_variables[t_idx] = set()
            self.live_clocks[t_idx] = []
            self.location_has_clockrates[t_idx] = {}
            for l_idx, l in enumerate(t.locations):
                self.max_constants[t_idx][l_idx] = {}
                self.upperbound[t_idx][l_idx] = {}
                self.lowerbound[t_idx][l_idx] = {}
                self.clockrates[t_idx][l_idx] = {}
                self.location_has_clockrates[t_idx][l_idx] = False
                for c in self._clocks:
                    self.max_constants[t_idx][l_idx][c] = -1
                    self.upperbound[t_idx][l_idx][c] = -1
                    self.lowerbound[t_idx][l_idx][c] = -1
                    self.clockrates[t_idx][l_idx][c] = 1

    def parse_and_calculate_constants(self):
        self.lex = lexer.lexer
        try:
            self.pars = parser.Parser(self.nta.declaration, self.lex)
        except Exception:
            opaal.util.emergencyExitUppaalCParser("Error in parsing the model to calculation constants.")
        self.declvisitor = parser.DeclVisitor(self.pars)
        self.declvisitor.visit(self.pars.AST) 

        self.constants = {}
        #constant overrides
        for (cident, cval) in self.constant_overrides.iteritems():
            #XXX assumes expression is already python
            self.constants[cident] = eval(cval, {}, self.constants)
        #evaluate constants to values
        for (cident, cval) in self.declvisitor.constants.iteritems():
            if not cident in self.constants:
                self.constants[cident] = eval(util.expression_to_python(cval), {}, self.constants)

        try:
            #evaluate VarDecl expressions
            for vdecl in self.declvisitor.variables:
                util.eval_vardecl_expressions(vdecl, self.constants)
        except Exception:
            opaal.util.emergencyExitUppaalCParser("Error in evaluating variable properties (e.g. array dimensions), for '%s'." % (vdecl.identifier))

    def analyze(self):
        self.analyze_live_variables()
        self.analyze_lower_upperbounds()
        self.analyze_clockrates()

    #{{{ Live variable/clock analysis -- find variables that are live per. template
    def analyze_live_variables(self):
        for t_idx, t in enumerate(self.nta.templates):
            local_collect_variables = partial(self._collect_variables, t_idx=t_idx)
            logger.debug("In template %s:", t.name)
            for l_idx, l in enumerate(t.locations):
                if l.invariant.value:
                    ast = expressionParser.parse_expression(l.invariant.value)
                    if ast:
                        ast.visit(local_collect_variables)
            #outgoing transitions
            for trans in t.transitions:
                #guard
                if trans.guard.value:
                    ast = expressionParser.parse_expression(trans.guard.value)
                    ast.visit(local_collect_variables)
                if trans.assignment.value:
                    myparser = updateStatementParser.updateStatementParser(trans.assignment.value)
                    ast = myparser.parseUpdateStatements()
                    ast.visit(local_collect_variables)
            logger.debug("Live variables: \n %s", self.live_variables[t_idx])

    def _collect_variables(self, node, t_idx):
        if node.type == "Identifier":
            self.live_variables[t_idx].add(node.children[0])
        else:
            return True
    #}}}

    #{{{ Stopwatch/Clock rate analysis
    def analyze_clockrates(self):
        for t_idx, t in enumerate(self.nta.templates):
            for l_idx, l in enumerate(t.locations):
                if not l.invariant.value:
                    continue
                logger.debug("At loc %s:", l)
                s = l.invariant.value.split(';')
                statements = ";".join(s[:-1])
                ast = expressionParser.parse_expression(s[-1])
                #XXX, also do something with the statements
                local_collect_clockrates = partial(self._collect_clockrates, t_idx=t_idx, l_idx=l_idx)
                ast.visit(local_collect_clockrates)
            logger.debug("Clock rates: \n %s", self.clockrates[t_idx])
    
    def _collect_clockrates(self, node, t_idx, l_idx):
        if node.type in ('Greater', 'GreaterEqual', 
                'Less', 'LessEqual', 'Equal', 'NotEqual'):
            # Collect clock rates
            if node.children[0].type == 'ClockRate' and \
                    node.children[1].type != 'Identifier':
                self.has_clockrates = True
                self.location_has_clockrates[t_idx][l_idx] = True
                assert node.children[1].type == 'Number' and node.children[1].leaf in [0, 1]

                clockident = node.children[0]
                self.clockrates[t_idx][l_idx][clockident.leaf] = node.children[1].leaf
                logger.debug("Clock %s stopped in location %d", clockident.leaf, l_idx)
    #}}}

    #{{{ Lower-Upper bounds clock comparison analysis
    def _calc_index(self, t_idx, location_idx, clockname):
        return location_idx * len(self.live_clocks[t_idx]) + self.live_clocks[t_idx].index(clockname) + 1

    def _lu_collect_comparisons(self, node, t_idx, l_idx, lower_eq_graph, upper_eq_graph):
        if node.type in ('Greater', 'GreaterEqual', 
                'Less', 'LessEqual', 'Equal', 'NotEqual'):
            idents = [n for n in node.children if n.type == 'Identifier']
            clockside = None
            #is left side clock?
            if node.children[0].type == 'Identifier' and \
                    node.children[1].type != 'Identifier':
                clockident = node.children[0]
                exprnode = node.children[1]
                clockside = "left"
            #is right side clock?
            elif node.children[1].type == 'Identifier' and \
                    node.children[0].type != 'Identifier':
                clockident = node.children[1]
                exprnode = node.children[0]
                clockside = "right"
                if clockident.children[0] in self._clocks:
                    assert False, "Clock on the right of comparison not supported (%s, %s)" %  (clockident, exprnode)
                else:
                    #not a clock
                    return True
            #comparing two clocks?
            elif node.children[0].type == 'Identifier' and \
                    node.children[1].type == 'Identifier':
                clockident1 = node.children[0]
                clockident2 = node.children[1]
                #comparing clocks do not affect the max constants
                if clockident1.children[0] in self._clocks and clockident2.children[0] in self._clocks:
                    return True
                elif clockident1.children[0] in self._clocks:
                    #left side clock, right side some expression
                    clockident = clockident1
                    exprnode = node.children[1]
                    clockside = "left"
                elif clockident2.children[0] in self._clocks:
                    #right side clock, left side some expression
                    clockident = clockident2
                    exprnode = node.children[0]
                    clockside = "right"
                    assert False, "Clock on the right of comparison not supported"
                else:
                    #comparing two non-clocks
                    return True
            else:
                #Some expression we don't know about
                logger.warning("Unknown expression: %s", node)
                return True

            if not clockident.children[0] in self._clocks:
                return True

            #try to calc expression, might be constant
            try:
                constant = eval(util.expression_to_python(exprnode), {}, self.constants)
            except:
                #variables in expression
                a = util.range_for_expression(exprnode, self.declvisitor, self.constants)
                constant = a[1]

            logger.debug("    found comparison of %s to %d", clockident.children[0], constant)

            # lower bound
            if node.type in ('Greater', 'GreaterEqual', 'Equal', 'NotEqual') and clockside == "left":
                lower_eq_graph[self._calc_index(t_idx, l_idx, clockident.children[0])][0] = \
                        max(constant, lower_eq_graph[self._calc_index(t_idx, l_idx, clockident.children[0])][0])
            # upper bound -- not an elif!
            if node.type in ('Less', 'LessEqual', 'Equal', 'NotEqual') and clockside == "left":
                upper_eq_graph[self._calc_index(t_idx, l_idx, clockident.children[0])][0] = \
                        max(constant, upper_eq_graph[self._calc_index(t_idx, l_idx, clockident.children[0])][0])

        return True

    def _collect_resets(self, node, src_idx, dst_idx, clocks_reset):
        if node.type in ('Assignment',):
            if node.children[0].children[0].type not in ['PlusPlusPost', 'MinusMinusPost']:

                #is left side clock?
                if node.leaf.type == 'Identifier' and \
                        node.leaf.children[0] in self._clocks:
                    clockident = node.leaf.children[0]
                    exprnode = node.children[0]
                else:
                    #another assignment, we don't care about
                    return False

                if node.children[0].children[0].type == 'Number':
                    #reset to a constant
                    pass
                elif node.children[0].children[0].type == 'Identifier':
                    #reset to a variable
                    if self.declvisitor.get_vardecl(node.children[0].children[0].children[0]):
                        pass
                    else:
                        assert False, "Reset of clock to unknown expression"
                else:
                    assert False, "Reset of clock to unknown expression"

                logger.debug("    found reset of %s", clockident)
                clocks_reset[clockident] = True

        return True

    def analyze_lower_upperbounds(self):
        """
        Location dependent lower-upper bounds analysis, as described in
        "Static Guard Analysis in Timed Automata Verification" by 
        Gerd Behrmann, Patricia Bouyer, Emmanuel Fleury and Kim G. Larsen
        and
        "Lower and Upper Bounds in Zone Based Abstractions of Timed Automata" by 
        Gerd Behrmann, Patricia Bouyer, Kim G. Larsen and Radek Pelanek

        Uses the more general form of analysis, which is O(n^3). If only certain 
        kinds of clock guards/resets are needed the O(n) algorithm can be implemented.

        Currently only handles updates of the form x := c, but could be expanded.
        Assumes all clocks are global.
        """

        #Collect inequalities
        for t_idx, t in enumerate(self.nta.templates):
            self.live_clocks[t_idx] = [c for c in self._clocks if c in self.live_variables[t_idx]]
            logging.debug("Live clocks for %s: %s", t.name, self.live_clocks[t_idx])
            numclocks = len(self.live_clocks[t_idx])
            clocks_reset_proto = {}
            for c in self.live_clocks[t_idx]:
                clocks_reset_proto[c] = False
            #init empty graph
            numlocs = len(t.locations)
            logger.debug("Matrix of size %dx%d (%d locations, %d clocks)", numlocs*numclocks+1, numlocs*numclocks+1, numlocs, numclocks)
            lower_eq_graph = numpy.empty([numlocs*numclocks+1, numlocs*numclocks+1], dtype=int)
            lower_eq_graph.fill(-1)
            upper_eq_graph = numpy.empty([numlocs*numclocks+1, numlocs*numclocks+1], dtype=int)
            upper_eq_graph.fill(-1)

            for l_idx, l in enumerate(t.locations):
                if not l.invariant.value:
                    continue
                logger.debug("At loc %s:", l)
                s = l.invariant.value
                ast = expressionParser.parse_expression(s)
                local_collect_comparisons = partial(self._lu_collect_comparisons, t_idx=t_idx, l_idx=l_idx, 
                        lower_eq_graph=lower_eq_graph, upper_eq_graph=upper_eq_graph)
                ast.visit(local_collect_comparisons)

            #outgoing transitions
            for trans in t.transitions:
                source_id = t.locations.index(trans.source)
                target_id = t.locations.index(trans.target)
                #guard
                if trans.guard.value:
                    ast = expressionParser.parse_expression(trans.guard.value)
                    local_collect_comparisons = partial(self._lu_collect_comparisons, t_idx=t_idx, l_idx=source_id, 
                            lower_eq_graph=lower_eq_graph, upper_eq_graph=upper_eq_graph)
                    ast.visit(local_collect_comparisons)

                #dependencies through non-resetting
                for c in self.live_clocks[t_idx]:
                    lower_eq_graph[self._calc_index(t_idx, source_id, c)][self._calc_index(t_idx, target_id, c)] = -1
                    upper_eq_graph[self._calc_index(t_idx, source_id, c)][self._calc_index(t_idx, target_id, c)] = -1
                if trans.assignment.value:
                    myparser = updateStatementParser.updateStatementParser(trans.assignment.value)
                    ast = myparser.parseUpdateStatements()
                    if ast.children[0] is None:
                        logger.warning("couldn't parse update \"%s\", doing safe upper approximation", trans.assignment.value)
                        for c in self.live_clocks[t_idx]:
                            lower_eq_graph[self._calc_index(t_idx, source_id, c)] \
                                    [self._calc_index(t_idx, target_id, c)] = 0
                            upper_eq_graph[self._calc_index(t_idx, source_id, c)] \
                                    [self._calc_index(t_idx, target_id, c)] = 0
                    else:
                        clocks_reset = dict(clocks_reset_proto)
                        local_collect_resets = partial(self._collect_resets, src_idx=source_id, dst_idx=target_id, clocks_reset=clocks_reset)
                        ast.visit(local_collect_resets)

                        for (c, reset) in clocks_reset.iteritems():
                            if not reset:
                                lower_eq_graph[self._calc_index(t_idx, source_id, c)] \
                                        [self._calc_index(t_idx, target_id, c)] = 0
                                upper_eq_graph[self._calc_index(t_idx, source_id, c)] \
                                        [self._calc_index(t_idx, target_id, c)] = 0
                else:
                    for c in self.live_clocks[t_idx]:
                        lower_eq_graph[self._calc_index(t_idx, source_id, c)][self._calc_index(t_idx, target_id, c)] = 0
                        upper_eq_graph[self._calc_index(t_idx, source_id, c)][self._calc_index(t_idx, target_id, c)] = 0

            
            #logger.debug("lower_eq_graph: \n %s", lower_eq_graph)
            #logger.debug("upper_eq_graph: \n %s", upper_eq_graph)

            #Invert graph weights, to find longest paths instead
            lower_eq_graph = lower_eq_graph * -1
            upper_eq_graph = upper_eq_graph * -1

            #"1" now means no edge
            lower_eq_graph = self._all_pairs_shortest_path(lower_eq_graph, nan=1)
            upper_eq_graph = self._all_pairs_shortest_path(upper_eq_graph, nan=1)

            #invert graph back
            lower_eq_graph = lower_eq_graph * -1
            upper_eq_graph = upper_eq_graph * -1

            #logger.debug("lower_eq_graph, longest paths: \n %s", lower_eq_graph)
            #logger.debug("upper_eq_graph, longest paths: \n %s", upper_eq_graph)

            #collect output
            for l_idx, l in enumerate(t.locations):
                for c in self.live_clocks[t_idx]:
                    #for backwards compatibility
                    self.max_constants[t_idx][l_idx][c] = max(
                            lower_eq_graph[self._calc_index(t_idx, l_idx, c)][0],
                            upper_eq_graph[self._calc_index(t_idx, l_idx, c)][0])
                    self.lowerbound[t_idx][l_idx][c] = lower_eq_graph[self._calc_index(t_idx, l_idx, c)][0]
                    self.upperbound[t_idx][l_idx][c] = upper_eq_graph[self._calc_index(t_idx, l_idx, c)][0]

            logger.debug("lower bounds: \n %s", self.lowerbound[t_idx])
            logger.debug("upper bounds: \n %s", self.upperbound[t_idx])

    def _all_pairs_shortest_path(self, eq_graph, nan=None):
        """
        Floyd-Warshall in adjacency matrix eq_graph.

        @nan: the value used to denote no edge
        """
        numVertices = len(eq_graph)
        j = numpy.ones(numVertices, dtype=int)
        P = eq_graph

        for k in range(0, numVertices):
            col = P[:, k]
            row = P[k, :]
            a = numpy.outer(col, j)
            b = numpy.outer(j, row)
            
            a[:, row == nan] = nan
            b[col == nan, :] = nan

            P2 = a + b

            numpy.minimum(P, P2, P)

        return P


    def get_max_constants_for_state(self, state):
        """
        Return a dict: clock-name -> max constant
        valid for this state.

        Uses the "First Simple Case" for composition in
        "Static Guard Analysis in Timed Automata Verification" by 
        Gerd Behrmann, Patricia Bouyer, Emmanuel Fleury and Kim G. Larsen
        i.e. it is only correct for updates of the form x := c.
        """
        max_consts = {}
        for c in self._clocks:
            max_consts[c] = -1
            for t_idx, t in enumerate(self.nta.templates):
                l_idx = state.locs[t_idx]
                max_consts[c] = max(max_consts[c], 
                        self.max_constants[t_idx][l_idx][c])
        return max_consts


    #}}}

if __name__ == '__main__':
    import sys
    file = open(sys.argv[1])
    nta = pyuppaal.NTA.from_xml(file)
    logging.basicConfig( stream=sys.stderr, 
        level=logging.DEBUG)

    a = AnalyzeModel(nta)
    a.analyze()

    print a.max_constants
