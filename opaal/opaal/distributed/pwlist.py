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

from mpi4py import MPI
comm = MPI.COMM_WORLD
rank = comm.Get_rank()
size = comm.Get_size()

class DistributedPWList:
    """A wrapper for a normal PWList, that distributes states according to
    a distribution function."""

    def __init__(self, parent_pwlist, node):
        self.parent_pwlist = parent_pwlist
        self.node = node

    def __getattr__(self, name):
        """Wrap attribute accesses to also try the wrapped pwlist."""
        return getattr(self.parent_pwlist, name)

    def homenode(self, state):
        """Calculate the node this state belongs to."""
        try:
            return 1 + hash(state) % (size-1)
        except ZeroDivisionError:
            #Short-circuit for single or dual process case
            return size

    def stateInPwList(self, state):
        return self.parent_pwlist.stateInPwList(state)

    def addStateOwn(self, state):
        """Adds a state to the local pwlist. Used when we know the owner already."""
        self.parent_pwlist.addState(state)


    def addState(self, state):
        """Adds a state to the pwlist of the owning node."""
        recvnode = self.homenode(state)
        if rank == recvnode:
            self.parent_pwlist.addState(state)
        else:
            self.node.sendtoremote(state, recvnode)

    def getWaitingState(self):
        return self.parent_pwlist.getWaitingState()

# vim:ts=4:sw=4:expandtab
