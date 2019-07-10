### BEGIN LICENSE
# Copyright (C) 2011 Mads Chr. Olesen <mchro@cs.aau.dk>
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

from base_lattice import BaseTimeLattice

class DiscreteClock(BaseTimeLattice):
    """
    A clock implementing discrete time, that is time can be at an integer point
    and time "jumps" forward in intervals of 1.
    """

    def __init__(self, dimensions=None, name=None, context=None):
        #Only allow singleton
        assert(dimensions==None or dimensions==[])
        self.clock = 0
        self.name = name

        self.set_max_constant(10) #some number, users should call method themselves!

    def covers(self, other):
        """
        Degenerate partial order, is actually equality of timepoints.
        """
        return self.clock == other.clock

    def __eq__(self, other):
        return self.clock == other.clock

    def join(self, other):
        #join not supported
        abstract

    delay_is_inclusive = False
    def delay(self):
        if self.clock <= self.cmax:
            self.clock += 1
            return True
        else:
            return False

    def reset(self):
        self.clock = 0

    def set_max_constant(self, cmax):
        self.cmax = cmax
        if self.clock > self.cmax:
            self.clock = self.cmax + 1
        #XXX, should we check whether we only decrease the max constant?
        #or something else to make sure the MC is sound?
        #allow seq cmax1 > cmax2 > ... > -1, and then start over?

    def __cmp__(self, other):
        return self.clock - int(other)

    def __int__(self):
        return int(self.clock)

    def __repr__(self):
        return "DiscreteClock: %d" % (self.clock)
