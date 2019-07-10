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

from collections import defaultdict

from opaal.passed_waiting_list import NoMoreStatesException, GoalFoundException

import logging
logger = logging.getLogger('lattice_pwlist')
#logger.setLevel(logging.DEBUG)

class LatticeCoverPWList(object):
    """PWList that does simple coverage checking (whether a state is already 
    "covered" by another state). Uses the partial ordering of states.
    
    States should only hash on the discrete part, and have a defined covers
    operator on the lattice part."""

    def __init__(self):
        self.waiting = []

        #map from discrete part to bucket of states with differing lattice parts
        self.passed_waiting = defaultdict(list)

        #number of successful adds to passed-waiting list
        self.num_adds = 0

    def stateInPwList(self, state):
        """Check if state is covered.
        Returns False if state was not seen before,
        returns a covering state if state was covered"""
        bucket = self.passed_waiting[hash(state)]

        for s in bucket:
            if s.covers(state):
                return s
        return False

    def addState(self, state):
        """Add a state to the passed-waiting list.
        @returns: state if state was new, covering state if state was covered by some other state."""
        covering_state = self.stateInPwList(state)
        if not covering_state:
            for otherw in self.waiting:
                if state.covers(otherw):
                    self.waiting.remove(otherw)
            self.waiting.append(state)
            self.passed_waiting[hash(state)].append(state)
            self.num_adds += 1
            return state
        return covering_state

    def getWaitingState(self):
        try:
            return self.waiting.pop(0)
        except IndexError:
            raise NoMoreStatesException()

    def lenOfPWList(self):
        return sum([len(b) for b in self.passed_waiting.itervalues()])

class LatticeJoinPWList(LatticeCoverPWList):
    """PWList that joins states according to a oracle joining function, and checks coverage"""

    def __init__(self, oracle_joining=None, trackjoins=False):
        super(LatticeJoinPWList, self).__init__()

        if oracle_joining == None:
            #join everything
            oracle_joining = lambda x,y: True
            #oracle_joining = lambda x,y: (x['aLogin'].num0s() + y['aLogin'].num0s()) < x['aLogin'].size
        self.oracle_joining = oracle_joining
        self.trackjoins = trackjoins

    def addState(self, state):
        """Add a state to the passed-waiting list.
        @returns: state if state was new, joined state if it was joined with some other state,
        covering state if state was covered by some other state."""
        covering_state = self.stateInPwList(state)
        if not covering_state:
            bucket = self.passed_waiting[hash(state)]
            
            for s in bucket:
                #should we join with this element?
                if s.discrete_eq(state) and self.oracle_joining(s, state):
                    logger.debug("Joining:")
                    logger.debug(str(s))
                    logger.debug(str(state))
                    join_state = s.join(state)
                    if self.trackjoins:
                        join_state.joined = (s, state)
                    logger.debug("Result: %s", str(join_state))
                    bucket.remove(s)
                    #for ws in self.waiting:
                    #    if ws <= join_state:
                    #        self.waiting.remove(ws)
                    try:
                        self.waiting.remove(s)
                    except ValueError:
                        pass
                    bucket.append(join_state)
                    self.waiting.append(join_state)
                    self.num_adds += 1
                    return join_state
            #no joining should occur
            bucket.append(state)
            self.waiting.append(state)
            self.num_adds += 1
            return state
        return covering_state

        

# vim:ts=4:sw=4:expandtab
