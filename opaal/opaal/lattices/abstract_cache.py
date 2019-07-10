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

class AbstractCache(BaseLattice):
    """Abstract LRU cache.
    See "Cache Behavior Prediction by Abstract Interpretation"
    by Alt, Martin and Ferdinand, Christian and Martin, Florian and Wilhelm, Reinhard, 
    """

    def __init__(self, dimensions=None, name=None, cachelines=None, context=None):
        dimensions = dimensions or (8, )
        #XXX only 1 dimension supported
        assert len(dimensions) == 1

        self.num_cachelines = dimensions[0]
        if not cachelines:
            self.cachelines = [set() for i in range(self.num_cachelines)]
        else:
            self.cachelines = copy.copy(cachelines)

    def join(self, other):
        return self.must_join(other)

    def must_join(self, other):
        """Abstract LRU cache must join function.
        Section 6.2 in paper."""
        res = AbstractCache(dimensions=(self.num_cachelines,))

        seen_memitems = set()

        for line in range(self.num_cachelines):
            for item in self.cachelines[line]:
                if item in seen_memitems:
                    res.cachelines[line].add(item)
                    seen_memitems.remove(item)
                else:
                    seen_memitems.add(item)

            for item in other.cachelines[line]:
                if item in seen_memitems:
                    res.cachelines[line].add(item)
                    seen_memitems.remove(item)
                else:
                    seen_memitems.add(item)
        return res


    def access(self, memitem):
        """Abstract LRU cache access/update function.
        Definition 4 in paper.
        
        @returns True on hit, False on miss"""
        #check for hit (move memitem from current set to front)
        for line in range(self.num_cachelines):
            try:
                self.cachelines[line].remove(memitem)
                #hit found
                h = line
                for i in range(h, 0, -1):
                    self.cachelines[i] = self.cachelines[i-1]
                self.cachelines[0] = set([memitem])
                return True
            except KeyError:
                pass

        #LRU access policy!
        for i in range(self.num_cachelines-1, 0, -1):
            self.cachelines[i] = self.cachelines[i-1]
        self.cachelines[0] = set([memitem])
        return False

    def ishit(self, memitem):
        """@returns True if an access to memitem would result in a hit, False on miss"""
        #check for hit (move memitem from current set to front)
        for line in range(self.num_cachelines):
            if memitem in self.cachelines[line]:
                return True
        return False

    def __str__(self):
        return "AbstractCache " + str(self.cachelines)

    def __repr__(self):
        return "AbstractCache(%d, %s)" % (self.num_cachelines, repr(self.cachelines))

    def __eq__(self, other):
        if self.num_cachelines != other.num_cachelines:
            return False
        for line in range(self.num_cachelines):
            if self.cachelines[line] != other.cachelines[line]:
                return False
        return True

# vim:ts=4:sw=4:expandtab
