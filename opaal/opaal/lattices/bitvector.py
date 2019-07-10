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
from base_lattice import BaseLattice

import logging
logger = logging.getLogger('bitvector')
#logger.setLevel(logging.DEBUG)

import numpy

class BitVector(BaseLattice):
    def __init__(self, dimensions=None, name=None, vector=None, context=None):
        dimensions = dimensions or (1, )

        self.size = dimensions
        if vector is None:
            vector = numpy.zeros(dimensions, dtype=bool)
        self.vector = vector
        #self.vector = [0 for i in range(self.size)]

    def join(self, other):
        abstract

    def meet(self, other):
        abstract

    def __getitem__(self, key):
        return self.vector[key]

    def __setitem__(self, key, value):
        logger.debug('setting %d to %s', key, value)
        value = value and 1 or 0
        self.vector[key] = value

    def __str__(self):
        return "BitVector " + str(self.vector)

    def __repr__(self):
        return str(self)

    def __eq__(self, other):
        if self.size != other.size:
            return False
        return numpy.alltrue(self.vector == other.vector)

    def num1s(self):
        return len([x for x in self.vector if x])
    def num0s(self):
        return len([x for x in self.vector if not x])

    def clearall(self):
        self.vector = numpy.zeros(dimensions, dtype=bool)

    def setall(self):
        self.vector = numpy.ones(dimensions, dtype=bool)


class UnionBitVector(BitVector):
    def join(self, other):
        assert self.size == other.size
        return UnionBitVector(dimensions=self.size, vector=(self.vector | other.vector))

    def covers(self, other):
        assert self.size == other.size

        return numpy.alltrue(other.vector <= self.vector)

class IntersectionBitVector(BitVector):
    """BitVector with join as intersection, and covers as reverse subset inclusion."""
    def join(self, other):
        assert self.size == other.size
        return IntersectionBitVector(dimensions=self.size, vector=(self.vector & other.vector))

    def covers(self, other):
        assert self.size == other.size

        return numpy.alltrue(other.vector >= self.vector)
