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

class BaseLattice(object):
    """
    In general all operations work as:
    opX(arg1, arg2, ...) and returning a string containing C-code, that will perform
    the given operation on self.name
    """
    def __init__(self, name=None, dimensions=None, context=None):
        pass

    def generateExtraLatticeFunctions(self):
        return ""

    @classmethod
    def getCompilerLinkFlags(cls):
        return ""

    def generateLatticeHashPart(self, a):
        return "42 /* XXX hash for real */"

    def generateApplyInvariantPart(self, out):
        return ""

    def generateCallbackPart(self, out):
        return ""

    def addChildVariable(self, vtype, vident, vdimensions):
        """
        Add an extern child variable, e.g. "oct.int myint;" should make the
        identifier "myint" be valid for e.g. function calls to the parent
        variable in some domain specific way.
        """
        abstract

    def allocate(self):
        abstract

    def join(self, other):
        abstract

    def meet(self, other):
        abstract
