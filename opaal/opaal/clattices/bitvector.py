# -*- coding: utf-8 -*-
### BEGIN LICENSE
# Copyright (C) 2013 Mads Chr. Olesen <mchro@cs.aau.dk>
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

import logging
logger = logging.getLogger('cbitvector')
#logger.setLevel(logging.DEBUG)

class BitVector(BaseLattice):
    """
    BitVector implementation generating C++ code.
    """
    def __init__(self, dimensions=None, name=None, context=None):
        dimensions = dimensions or (1, )
        assert len(dimensions) == 1, "BitVector only supports one dimension"
        self.dimensions = dimensions
        self.name = name
        self.context = context

    def generateHeader(self):
        return "#include <bitset>\n#include <iostream>\n"

    def generateStateStructPart(self):
        return "std::bitset<%d> *%s;" % (self.dimensions[0], self.name);

    def generateInitialStatePart(self):
        return "NULL, /* %s */" % (self.name)

    def generateInitialFuncPart(self, state_name):
        return "%s.%s = new std::bitset<%d>();" % \
            (state_name, self.name, self.dimensions[0])

    def generateCopyPart(self, in_state_name, out_state_name):
        return "std::bitset<%(d)d> %(out)s%(sname)s(*%(in)s->%(sname)s); %(out)s->%(sname)s = &%(out)s%(sname)s;" % {
            'd': self.dimensions[0], 'out': out_state_name, 'sname': self.name, 'in': in_state_name
            }

    def generateLatticePrintPart(self, name):
        return "return ((std::bitset<%d>*)%s)->to_string().c_str();" % (
                self.dimensions[0], name);

    def generateLatticeClonePart(self, a):
        return "new std::bitset<%d>( (*(std::bitset<%d>*)%s) );" % (
                self.dimensions[0], self.dimensions[0], a);

    def generateLatticeDeletePart(self, a):
        return "delete ((std::bitset<%d>*)%s);" % (
                self.dimensions[0], a);

    def generateLatticeCmpPart(self, a, b):
        return "((*(std::bitset<%d>*)%s) == (*(std::bitset<%d>*)%s))" % (
                self.dimensions[0], a,
                self.dimensions[0], b,
                )

    def join(self, other):
        abstract

    def meet(self, other):
        abstract

    # Operations {{{
    #XXX think about how to hook these into the c-code generation
    def __getitem__(self, key):
        return "out->%s[%s]" % (self.name, key)

    def __setitem__(self, key, value):
        return "out->%s[%s] = %s;" % (self.name, key, value)
    #}}}


class UnionBitVector(BitVector):
    def generateJoinPart(self, a, b):
        """ a = a join b"""
        return "(*(std::bitset<%(d)d>*)%(a)s) |= (*(std::bitset<%(d)d>*)%(b)s); return 1;" % {
                'd': self.dimensions[0], 'a': a, 'b': b
                }

    def generateCoverPart(self, a, b):
        """a <= b"""
        return "((**(std::bitset<%(d)d>**)%(a)s) | (**(std::bitset<%(d)d>**)%(b)s)) == (**(std::bitset<%(d)d>**)%(b)s)" % {
                'd': self.dimensions[0], 'a': a, 'b': b
                }

class IntersectionBitVector(BitVector):
    """BitVector with join as intersection, and covers as reverse subset inclusion."""
    def join(self, other):
        TODO

    def generateCoverPart(self, a, b):
        """a <= b"""
        return "((**(std::bitset<%(d)d>**)%(a)s) & (**(std::bitset<%(d)d>**)%(b)s)) == (**(std::bitset<%(d)d>**)%(b)s)" % {
                'd': self.dimensions[0], 'a': a, 'b': b
                }
