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

import util

import logging
logger = logging.getLogger('goalchecker')

from pyuppaal.ulp import expressionParser

class GoalChecker:
    def __init__(self, succgen, query):
        self.succgen = succgen
        self.query = query
        self.query_type = None

        #Short-circuit, if no query:
        if query == "":
            self.isGoal = lambda s: False
            return

        #Parse query, and compile goal status query XXX
        self.query_type = query.strip()[:3]

        if self.query_type == "E<>":
            #form: E<> some_expression
            query = (query.strip()[3:]).strip()
            query_ast = expressionParser.parse_expression(query)
            self.goal_func_python = util.expression_to_python(query_ast, self.succgen)
            logger.info('Goal func: %s', self.goal_func_python)
            self.goal_expr = compile(self.goal_func_python, "<goal func>", 'eval')
            self.isGoal = self.isGoal_reachability
        elif self.query_type == "sup":
            #form: sup: some_expression
            self.sup_val = None
            query = (query.strip()[4:]).strip()
            query_ast = expressionParser.parse_expression(query)
            self.sup_expr_python = util.expression_to_python(query_ast, self.succgen)
            logger.info('sup expr.: %s', self.sup_expr_python)
            self.sup_expr = compile(self.sup_expr_python, "<goal func>", 'eval')
            self.isGoal = self.isGoal_sup
        else:
            raise IllegalQueryException(
                'Sorry, only reachability ("E<>") and sup supported for now')

    def isGoal(self, state):
        abstract


    def isGoal_reachability(self, state):
        if eval(self.goal_expr, self.succgen.constants, state):
            #print "Goal reached:", state.locs, self.goal_func_python
            return True
        return False 

    def isGoal_sup(self, state):
        state_sup_val = eval(self.sup_expr, self.succgen.constants, state)
        logger.debug('Comparing %s and %d', self.sup_val, state_sup_val)
        if self.sup_val is None:
            self.sup_val = int(state_sup_val)
            logger.debug('Should only happen once!')
        elif int(state_sup_val) > self.sup_val:
            self.sup_val = int(state_sup_val)
        logger.debug('Result: %d', self.sup_val)

    def finalize(self):
        """Should be called when the entire state space has been explored.
        @returns answer to asked query."""
        if self.query_type == "sup":
            return self.sup_val

# vim:ts=4:sw=4:expandtab
