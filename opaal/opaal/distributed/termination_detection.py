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

from mpi4py import MPI
comm = MPI.COMM_WORLD
rank = comm.Get_rank()
size = comm.Get_size()

from numpy import array
import messages

#Colors for termination detection
( WHITE, BLACK ) = range(2)

class TerminationDetection:
    """Termination detection, implementation of
    "Derivation of a termination detection algorithm for distributed computations"
    by Dijkstra, Feijen and Gasteren"""
    def __init__(self, node):
        self.node = node

        self.has_term_detect_token = False
        self.term_detect_color = BLACK
        self.has_work = True
        self.terminated = False

    def sentMessage(self):
        """Node sent a message, mark as black"""
        self.term_detect_color = BLACK

    def noMoreWork(self):
        """Node has no more work, pass the token on, if applicable"""
        self.has_work = False
        if self.has_term_detect_token:
            #print "Rank %d passing on term detect token" % (rank)
            self.termination_detection_received()

    def moreWork(self):
        self.has_work = True

    def setupMessageHandler(self):
        #MSG_TERMINATION_DETECTION {{{
        self.termination_detection_req = array(0, dtype=int)
        self.termination_detection_prequest = comm.Recv_init([self.termination_detection_req, MPI.INT], source=MPI.ANY_SOURCE, 
            tag=messages.TERMINATION_DETECTION)
        self.node.computation_reqlist += [self.termination_detection_prequest]
        self.node.computation_reqhandlers += [self.termination_detection_received]
        #}}}
        #print "Rank %d inited term detection" % (rank)

    def master_start_termination_detection(self):
        self.setupMessageHandler()
        MPI.Prequest.Start(self.termination_detection_prequest)
        self.master_send_term_detect_token()

    def master_send_term_detect_token(self):
        tosend = array(self.term_detect_color, dtype=int)
        #print "Master sending to ", (rank+1)%size
        comm.Bsend([tosend, MPI.INT], dest=(rank+1)%size, tag=messages.TERMINATION_DETECTION)

    def master_termination_detection(self):
        #print "Master term detect"
        if self.termination_detection_prequest.Test():
            token = self.termination_detection_req
            #print "master received:", token == WHITE
    
            if token == WHITE and self.term_detect_color == WHITE:
                self.terminated = True
                print "Master reporting: Termination detected!"
            else:
                self.term_detect_color = WHITE
                self.master_send_term_detect_token()

            self.termination_detection_prequest.Start()

    def slave_init(self):
        self.term_detect_color = BLACK
        self.setupMessageHandler()

    def termination_detection_received(self):
        token = self.termination_detection_req
        #print "received:", token, "self is:", self.term_detect_color, token == WHITE

        #If inactive, pass it on
        if not self.has_work:
            self.has_term_detect_token = False
            if token == WHITE and self.term_detect_color == WHITE:
                tosend = array(WHITE, dtype=int)
                #print "Sending WHITE term_detect from", rank
                comm.Bsend([tosend, MPI.INT], dest=(rank+1)%size, tag=messages.TERMINATION_DETECTION)
            else:
                tosend = array(BLACK, dtype=int)
                #print "Sending BLACK term_detect from", rank
                comm.Bsend([tosend, MPI.INT], dest=(rank+1)%size, tag=messages.TERMINATION_DETECTION)
                self.term_detect_color = WHITE
        else:
            self.has_term_detect_token = True

# vim:ts=4:sw=4:expandtab
