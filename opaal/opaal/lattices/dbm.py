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

from pydbm import udbm
from base_lattice import BaseTimeLattice

class DBMFederation(udbm.Federation, BaseTimeLattice):
    context_to_federation = {}

    def __init__(self, name=None, dimensions=None, context=None, dbmcontext=None):
        #To be compatible with udbm.Federation constructor
        if isinstance(name, udbm.Context) and dimensions == None and context == None and dbmcontext == None:
            dbmcontext = name
            name = None

        #Only allow singleton
        assert(dimensions==None or dimensions==[])

        DBMFederation.context_to_federation[context] = self

        dbmcontext = dbmcontext or udbm.Context([], name=name)
        udbm.Federation.__init__(self, dbmcontext)

    def add_clock(self, name=None, dimensions=None, context=None):
        assert(DBMFederation.context_to_federation[context] == self)

        #XXX handle dimensions
        assert(dimensions==None or dimensions==[])

        #delete the old clock attributes
        for c in self.context.clocks:
            delattr(self, c.name)
        self.context.addClockByName(name)
        #create new clock attributes
        udbm.Federation.__init__(self, self.context)

    delay = udbm.Federation.upInPlace
    may_delay = udbm.Federation.upInPlace

    def covers(self, other):
        return (other <= self)

    def __str__(self):
        return udbm.Federation.__str__(self)
    __repr__ = __str__

    def __bool__(self):
        return self.isEmpty()

def DBMClock(name=None, dimensions=None, context=None):
    federation = DBMFederation.context_to_federation[context]
    federation.add_clock(name, dimensions, context)
    return None
