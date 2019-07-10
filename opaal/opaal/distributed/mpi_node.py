
from mpi4py import MPI
import messages
import datetime


comm = MPI.COMM_WORLD
rank = comm.Get_rank()
size = comm.Get_size()

from numpy import array

from opaal.model_parsers.pyuppaal import SuccessorGenerator, GoalChecker
from opaal.passed_waiting_list import SimplePWList
from opaal.modelchecking_algorithms.reachability import McReachability, NoMoreStatesException, GoalFoundException

from termination_detection import TerminationDetection
from pwlist import DistributedPWList

class MPINode: #XXX, change name to SlaveNode?
    """A MPI Slave node. This class is responsible for running the slave main loop:
    * Doing a little communication
    * Doing a little computation
    * Profit!"""

    def __init__(self, model, query):
        self.model = model
        self.query = query

        self.reqlist = []
        self.reqhandlers = []
        self.control_reqlist = []
        self.control_reqhandlers = []
        self.computation_reqlist = []
        self.computation_reqhandlers = []

        self.goal_reached = False

        self.termination_detection = TerminationDetection(self)

        self.succgen = SuccessorGenerator(self.model)
        self.goalchecker = GoalChecker(self.succgen, self.query)
        self.pwlist = DistributedPWList(SimplePWList(), self)
        self.mcReachability = McReachability(self.succgen, self.goalchecker, self.pwlist)

    def sendstate(self, state):
        #send state to node
        recvnode = self.homenode(state)
        if rank == recvnode:
            if not state in self.passed_waiting: #and not state in self.waiting:
                self.waiting.append(state)
                self.passed_waiting.add(state)

        else:
            sendtoremote(state, recvnode)

    def sendtoremote(self, state, recvnode):
        self.termination_detection.sentMessage()
        #print "Sending state, %d -> %d" % (rank, recvnode)
        #TODO: serialize to numpy array!!!!
        comm.send(state, dest=recvnode, tag=messages.STATE)

    #XXX
    def master_goal_detection(self):
        return False
        if self.goal_reached_prequest.Test():
            #self.goal_reached_received()
            self.goal_reached = True
            return True
        return False

    #XXX
    def setupGoalMessageHandler(self):
        return
        #messages.GOAL_REACHED {{{
        self.goal_reached_req = array(0, dtype=int)
        self.goal_reached_prequest = comm.Recv_init([self.goal_reached_req, MPI.INT], source=MPI.ANY_SOURCE, tag=messages.GOAL_REACHED)
        self.computation_reqlist += [self.goal_reached_prequest]
        self.computation_reqhandlers += [self.goal_reached_received]
        #}}}

    def slave(self): #{{{
        #setup prerequests
        #messages.STATUS {{{
        self.status_reqs = array(0, dtype=int)
        self.status_prequest = comm.Recv_init([self.status_reqs, MPI.INT], source=0, tag=messages.STATUS)
        self.control_reqlist += [self.status_prequest]
        self.control_reqhandlers += [self.status]
        #}}}
        #messages.ABORT {{{
        self.abort_reqs = array(0, dtype=int)
        self.abort_prequest = comm.Recv_init([self.abort_reqs, MPI.INT], source=0, tag=messages.ABORT)
        self.control_reqlist += [self.abort_prequest]
        self.control_reqhandlers += [self.abort]
        #}}}
        #messages.STATE {{{
        self.state_req = array([0]*300, dtype='uint8') #XXX, calculate exact state size
        self.state_prequest = comm.Recv_init([self.state_req, MPI.BYTE], source=MPI.ANY_SOURCE, tag=messages.STATE)
        self.computation_reqlist += [self.state_prequest]
        self.computation_reqhandlers += [self.state_received]
        #}}}

        self.setupGoalMessageHandler()
        self.termination_detection.slave_init()

        self.reqlist = self.control_reqlist + self.computation_reqlist
        self.reqhandlers = self.control_reqhandlers + self.computation_reqhandlers

        #print self.reqlist, self.reqhandlers

        #MPI buffer send space
        MPI.Attach_buffer(MPI.Alloc_mem(1024*1024)) #1Mb

        MPI.Prequest.Startall(self.reqlist)
        print "Slave", rank, "awaiting your command"

        self.running = True
        while self.running:
            #Do control comm, if any
            (i, comm_todo) = MPI.Prequest.Testany(self.control_reqlist)
            if comm_todo:
                self.control_reqhandlers[i]()
                self.control_reqlist[i].Start()
            #Do computation comm, if any
            (i, comm_todo) = MPI.Prequest.Testany(self.computation_reqlist)
            if comm_todo:
                #print "calling ", self.computation_reqhandlers[i]
                self.computation_reqhandlers[i]()
                self.computation_reqlist[i].Start()

            #Do a computation
            try:
                self.mcReachability.compute()
            except NoMoreStatesException:
                #No more work...
                #print "Rank %d has no more work, len(pwlist) = %d" % (rank, len(self.pwlist.waiting))
                self.termination_detection.noMoreWork()
                #... wait for something to arrive
                i = MPI.Prequest.Waitany(self.reqlist)
                #print "calling ", self.reqhandlers[i]
                self.reqhandlers[i]()
                self.reqlist[i].Start()
            except GoalFoundException:
                #goal state found: Profit!
                comm.Bsend([None, MPI.INT], dest=0, tag=messages.GOAL_REACHED)
    #}}}

    #Slave callbacks {{{
    def abort(self):
        print "Slave %d: Aborting!" % (rank)
        self.running = False

    def status(self):
        #print "Slave %d: reporting!" % (rank)
        msg = (len(self.pwlist.waiting), len(self.pwlist.passed_waiting), self.mcReachability.processed_states)
        comm.send(msg, dest=0, tag=messages.STATUS)

    def state_received(self):
        #TODO: serialize to numpy array!!!!
        import cPickle as pickle
        state = pickle.loads(self.state_req.tostring())

        self.pwlist.addStateOwn(state)
        self.termination_detection.moreWork()
    #}}}

#XXX this should be moved
#if __name__ == "__main__":
#    model = None
#    if rank == 0:
#        #we're master, load model, do stuff, distribute it and start
#        model_file = open(sys.argv[1], "r")
#        model = pyuppaal.NTA.from_xml(model_file)
#        comm.bcast((model, ""), root=0)
#        #print "master: ", model
#
#        query = sys.argv[2] or ""
#
#        #start model checking
#        node = Node(model, query)
#        node.master()
#    else:
#        #wait for model
#        (model, query) = comm.bcast(None, root=0)
#        #print "slave:", model
#
#        #start model checking
#        node = Node(model, query)
#        node.slave()
#
# vim:ts=4:sw=4:expandtab
