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

from opaal import util

class NoMoreStatesException(util.Error):
    pass

class GoalFoundException(util.Error):
    pass

class SimplePWList:
    def __init__(self):
        self.waiting = []
        self.passed_waiting = set() 
        #number of successful adds to passed-waiting list
        self.num_adds = 0

    def stateInPwList(self, state):
        return state in self.passed_waiting

    def addState(self, state):
        """Add a state to the passed-waiting list.
        @returns: state if state was new, False if state was seen before"""
        if not self.stateInPwList(state):
            self.waiting.append(state)
            self.passed_waiting.add(state)
            self.num_adds += 1
            return state
        return False

    def getWaitingState(self):
        try:
            return self.waiting.pop()
        except IndexError:
            raise NoMoreStatesException()

    def lenOfPWList(self):
        return len(self.passed_waiting)

# vim:ts=4:sw=4:expandtab
