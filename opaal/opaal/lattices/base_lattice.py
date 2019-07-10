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

class BaseLattice(object):
    def __init__(self, name=None, dimensions=None, context=None):
        #TODO XXX standard crossproduct handling of dimensions
        #if dimensions:
        #    #handle array dimensions, using LatticeVector class
        #    latticebase = self.__class__(name=name)
        #    curval = latticebase
        #    for dim in reversed(array_dimensions):
        #        new_val = LatticeVector(curval, dim)
        #        curval = new_val
        #    initval = curval
        pass

    def join(self, other):
        abstract

    def covers(self, other):
        """Default covers operator.
        a covers b <=> a \join b = a
        """
        lub = self.join(other)
        if self == lub:
            return True
        else:
            return False

    def __eq__(self, other):
        abstract

    def __ne__(self, other):
        return not (self == other)

class LatticeVector(BaseLattice):
    """A vector of lattice elements. Comparison and join is component-wise."""

    def __init__(self, latticebase, size):
        """Create vector of size size, using class lattice"""
        self.size = size
        self.vector = [copy.deepcopy(latticebase) for i in range(size)]
        self.latticebase = latticebase

    def join(self, other):
        assert self.size == other.size

        res = LatticeVector(self.latticebase, self.size)
        for i in range(self.size):
            res[i] = self[i].join(other[i])
        return res

    def __str__(self):
        return str(self.vector)

    def __repr__(self):
        return str(self)

    def __getitem__(self, key):
        return self.vector[key]

    def __setitem__(self, key, value):
        self.vector[key] = value

    def __eq__(self, other):
        if self.size != other.size:
            return False
        for i in range(self.size):
            if self[i] != other[i]:
                return False
        return True

    def covers(self, other):
        assert self.size == other.size

        for i in range(self.size):
            if not self[i].covers(other[i]):
                return False
        return True

class BaseTimeLattice(BaseLattice):
    """
    Superclass of lattices representing time.
    """

    #Can a delay always be represented in a way that includes the current
    #time, i.e. x.delay().covers(x)
    delay_is_inclusive = False

    def delay(self):
        abstract

    def set_max_constant(self, cmax):
        abstract


# vim:ts=4:sw=4:expandtab
