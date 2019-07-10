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

class MaxInteger(BaseLattice):
    """A integer lattice (bottom: 0), with the ordering of the natural numbers, e.g. 43 covers 42
    Join is max, e.g. 42 join 43 = max(42, 43) = 43."""

    def __init__(self, dimensions=None, name=None, context=None):
        #XXX only 1 dimension supported
        assert(dimensions==None or dimensions==[])
        self.num = 0

    def __eq__(self, other):
        return self.num == int(other)

    def __cmp__(self, other):
        return self.num - int(other)

    def covers(self, other):
        return int(other) <= self.num

    def join(self, other):
        res = MaxInteger()
        res.num = max(self.num, int(other))
        return res

    #operations
    def __int__(self):
        return int(self.num)

    def __iadd__(self, other):
        self.num += int(other)
        return self

    def __str__(self):
        return str(self.num)

    def __repr__(self):
        return "MaxInteger " + str(self.num)

class MinInteger(BaseLattice):
    """A integer lattice (bottom: INT_MAX, top: INT_MIN), 
    with the reverse ordering of the natural numbers, e.g. 42 covers 43
    Join is min, e.g. 42 join 43 = min(42, 43) = 42."""

    def __init__(self, dimensions=None, name=None, context=None):
        #XXX only 1 dimension supported
        assert(dimensions==None or dimensions==[])
        self.num = 0

    def __eq__(self, other):
        return self.num == int(other)

    def __cmp__(self, other):
        return int(other) - self.num

    def covers(self, other):
        return self.num <= int(other)

    def join(self, other):
        res = MinInteger()
        res.num = min(self.num, int(other))
        return res

    #operations
    def __int__(self):
        return int(self.num)

    def __iadd__(self, other):
        self.num += int(other)
        return self

    def __str__(self):
        return str(self.num)

    def __repr__(self):
        return "MinInteger " + str(self.num)


