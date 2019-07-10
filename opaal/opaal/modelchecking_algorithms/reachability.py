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

from opaal.passed_waiting_list import NoMoreStatesException, GoalFoundException

class McReachability:
    def __init__(self, succgen, goalchecker, pwlist):
        self.succgen = succgen
        self.goalchecker = goalchecker
        self.pwlist = pwlist

        self.processed_states = 0

    def __1step(self):
        """Computes a single step."""
        state = self.pwlist.getWaitingState()
        if self.goalchecker.isGoal(state):
            raise GoalFoundException
        for succ in self.succgen.successors(state):
            self.pwlist.addState(succ)
            self.processed_states += 1

    def compute(self, steps=1):
        while steps > 0:
            self.__1step()
            steps -= 1

    def start(self):
        try:
            while True:
                self.__1step()
        except GoalFoundException:
            return True
        except NoMoreStatesException:
            self.goalchecker.finalize()
            return False

# vim:ts=4:sw=4:expandtab
