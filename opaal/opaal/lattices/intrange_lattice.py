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

from base_lattice import BaseLattice

class IntRange(BaseLattice):
    """A integer range lattice.
    
    Elements are pairs of (lowerbound, upperbound).
    (l1, u1) covers (l2, u2) <=> l1 <= l2 and u1 >= u2.
    (l1, u1) join (l2, u2) = (min(l1, l2), max(u1, u2))
    """

    def __init__(self, dimensions=None, name=None, context=None):
        #XXX only 1 dimension supported
        assert(dimensions==None or dimensions==[])
        self.l = 0
        self.u = 0

    def __eq__(self, other):
        return self.l == other.l and self.u == other.u

    def covers(self, other):
        return self.l <= other.l and self.u >= other.u

    def join(self, other):
        res = IntRange()
        res.l = min(self.l, other.l)
        res.u = max(self.u, other.u)
        return res

    #operations
    def __iadd__(self, other):
        if isinstance(other, int):
            self.l += int(other)
            self.u += int(other)
        elif isinstance(other, IntRange):
            self.l += other.l
            self.u += other.u
        else:
            assert False, "Invalid type for other %s" % other
        return self

    def __isub__(self, other):
        if isinstance(other, int):
            self.l -= int(other)
            self.u -= int(other)
        elif isinstance(other, IntRange):
            self.l -= other.u
            self.u -= other.l
        else:
            assert False, "Invalid type for other %s" % other
        return self

    def __str__(self):
        return "IntRange(%d, %d)" % (self.l, self.u)
    __repr__ = __str__
