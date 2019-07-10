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

from opaal import util

class IllegalStateException(util.Error):
    pass

class State:
    def __init__(self, succgen=None):
        self.vars = {}
        self.locs = {}
        self.clocks = {}
        self.lattice_part = {}
        self.hash = None

        self.succgen = succgen

    def recursive_list_to_tuple(self, l):
        tuplified = []
        for i in l:
            if isinstance(i, list):
                tuplified.append(self.recursive_list_to_tuple(i))
            else:
                tuplified.append(i)
        return tuple(tuplified)

    def __getitem__(self, key):
        if key == 'locs':
            return self.locs
        elif key == 'succgen':
            return self.succgen
        try:
            return self.clocks[key]
        except KeyError:
            try:
                return self.lattice_part[key]
            except KeyError:
                return self.vars[key]
    def __setitem__(self, key, value):
        self.hash = None
        if key in self.clocks.keys():
            if value == 0:
                #print 'Reseting clock %s' % (key)
                self.clocks[key] = value
            else:
                raise IllegalStateException("Assignment to clock %s not 0" % (key))
        elif key in self.lattice_part.keys():
            self.lattice_part[key] = value
        else:
            self.vars[key] = value

    def discrete_eq(self, other):
        #print "Comparing", self.locs, other.locs
        return self.clocks == other.clocks and self.vars == other.vars and \
            self.locs == other.locs

    def __eq__(self, other):
        """Precise equality operator."""
        return self.discrete_eq(other) and self.lattice_part == other.lattice_part

    def covers(self, other):
        """Cover relation: a covers b <=> a.discrete == b.discrete and a.lattice covers b.lattice"""
        if not self.discrete_eq(other):
            return False
        if self.lattice_part != {}:
            assert self.lattice_part.keys() == other.lattice_part.keys()
            for k in self.lattice_part.keys():
                if not (self.lattice_part[k].covers(other.lattice_part[k])):
                    return False
        return True

    def join(self, other):
        res = self.discrete_copy()
        if self.lattice_part != {}:
            assert self.lattice_part.keys() == other.lattice_part.keys()
            for k in self.lattice_part.keys():
                res.lattice_part[k] = self.lattice_part[k].join(other.lattice_part[k])
        return res

    def __hash__(self):
        """Hash like a tuple, see http://effbot.org/zone/python-hash.htm for details"""
        varstuple = self.recursive_list_to_tuple(self.vars)
        self.hash = self.hash or \
            hash(tuple(self.locs.values() + list(varstuple) + self.clocks.values()))
        return self.hash
        

    def __str__(self):
        if self.succgen:
            loc_labels = []
            for (t_idx, l_idx) in self.locs.iteritems():
                loc_labels.append(self.succgen.location_labels[t_idx].get(l_idx, str(l_idx)))
            loc_labels = "(" + ", ".join(loc_labels) + ")"
        else:
            loc_labels = str(self.locs)

        return "(" +  loc_labels + ", " + str(self.vars) + ", " + str(self.clocks) + \
                ", " + str(self.lattice_part) + ")"

    def discrete_copy(self):
        """Returns a copy of the discrete part of the state"""
        a = State(self.succgen)
        a.locs = self.locs.copy()
        a.vars = copy.deepcopy(self.vars)
        a.clocks = self.clocks.copy()
        return a

    def copy(self):
        """Returns a copy of this state"""
        a = self.discrete_copy()
        a.lattice_part = copy.deepcopy(self.lattice_part)
        return a

    def may_delay(self):
        """If a time delay can be represented, still encompassing the current
        time, do it."""
        #import pdb; pdb.set_trace()
        for l in self.lattice_part.itervalues():
            try:
                l.may_delay()
            except AttributeError:
                pass

    def delay(self):
        """Do a time delay, even if it changes the current time."""
        for l in self.lattice_part.itervalues():
            try:
                l.delay()
            except AttributeError:
                pass


# vim:ts=4:sw=4:expandtab
