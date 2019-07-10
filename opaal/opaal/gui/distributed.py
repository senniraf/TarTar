#!/usr/bin/python
from mpi4py import MPI
import sys
import os
comm = MPI.COMM_WORLD
rank = comm.Get_rank()
size = comm.Get_size()

print "Rank", rank, "on host", os.uname()[1]
from opaal.distributed import MPINode, messages

import gobject
import pygtk
pygtk.require("2.0")
import gtk

try:
    import matplotlib   
    matplotlib.use('GTK')   
    from matplotlib.figure import Figure   
    from matplotlib.axes import Subplot   
    from matplotlib.backends.backend_gtk import FigureCanvasGTK, NavigationToolbar
except ImportError:
    matplotlib = False
import numpy
import pyuppaal
import datetime
from opaal.opaalconfig import getdatapath

class MasterGui: 
    def __init__(self, filename=None, query=""):
        builder = gtk.Builder()
        builder.add_from_file(os.path.join(getdatapath(), "master_gui.ui"))
        self.root = builder.get_object('mainWin')
        builder.connect_signals(self)

        self.tlbStart = builder.get_object('tlbStart')
        self.tlbPause = builder.get_object('tlbPause')
        self.tlbStop = builder.get_object('tlbStop')
        self.statusbar = builder.get_object('statusbar1')
        self.imgQueryStatus = builder.get_object('imgQueryStatus')
        self.txtQueryQuery = builder.get_object('txtQueryQuery')

        self.graphContainer = builder.get_object('graphContainer')
        if matplotlib:
            # setup matplotlib stuff on first notebook page (empty graph) 
            #self.figure = Figure(figsize=(6,4), dpi=72) 
            self.figure = Figure() 
            self.axis = self.figure.add_subplot(111) 


            self.axis.set_xlabel('Time (secs.)') 
            self.axis.set_ylabel('Size of waiting list') 
            self.canvas = FigureCanvasGTK(self.figure) # a gtk.DrawingArea 
            self.canvas.show() 
            self.graphContainer.pack_start(self.canvas, True, True)

            self.graph_lines = []
            self.graph_data = []
            for i in range(1, size):
                self.graph_lines += self.axis.plot([0])
                self.graph_data += [[0]]

            print self.graph_data
            print self.graph_lines

            self.axis.set_ylim(0, 100)
            self.axis.set_xlim(0, 10)

        self.root.show_all()
        self.running = False
        
        if filename:
            self.loadFile(filename)
        if query:
            self.txtQueryQuery.set_text(query)
            gobject.idle_add(self.on_start)

    def on_quit(self, widget=None):
        for i in range(1, size):
            comm.send(None, dest=i, tag=messages.ABORT)
        gtk.main_quit()

    def on_openfile(self, widget=None):
        file_open_dialog = gtk.FileChooserDialog(title="Open UPPAAL model",
            action=gtk.FILE_CHOOSER_ACTION_OPEN,
                buttons=(gtk.STOCK_CANCEL,
                        gtk.RESPONSE_CANCEL,
                        gtk.STOCK_OPEN,
                        gtk.RESPONSE_OK))
        filter = gtk.FileFilter()
        filter.set_name("UPPAAL models")
        filter.add_pattern("*.xml")
        filter.add_mime_type("application/xml")
        file_open_dialog.add_filter(filter)

        filter = gtk.FileFilter()
        filter.set_name("All files")
        filter.add_pattern("*")
        file_open_dialog.add_filter(filter)

        if file_open_dialog.run() == gtk.RESPONSE_OK:
            filename = file_open_dialog.get_filename()
            self.loadFile(filename)
            file_open_dialog.destroy()
        else:
            file_open_dialog.destroy()

    def loadFile(self, filename):
        model_file = open(filename, "r")
        self.model = pyuppaal.NTA.from_xml(model_file)
        self.node = MPINode(self.model, self.txtQueryQuery.get_text())
        print "Master Broadcasting..."
        comm.bcast((self.model, self.txtQueryQuery.get_text()), root=0)

    def on_start(self, widget=None):
        self.running = True
        self.tlbStart.set_sensitive(False)
        self.tlbPause.set_sensitive(True)
        self.tlbStop.set_sensitive(True)
        self.start_time = datetime.datetime.now()

        #Seed the modelchecking with the initial state
        initstate = self.node.succgen.get_initialstate()
        self.node.sendtoremote(initstate, self.node.pwlist.homenode(initstate))

        self.node.termination_detection.master_start_termination_detection()

        gobject.timeout_add(100, self.on_process_mpi)
        gobject.timeout_add(1000, self.on_update_status)

    def on_pause(self, widget=None):
        #Broadcast pause
        #for i in range(1, size):
        #    comm.send(None, dest=i, tag=messages.PAUSE)
        self.tlbStart.set_sensitive(True)
        self.tlbPause.set_sensitive(False)
        self.tlbStop.set_sensitive(True)
        self.running = False

    def on_abort(self, widget=None):
        self.tlbStart.set_sensitive(True)
        self.tlbPause.set_sensitive(False)
        self.tlbStop.set_sensitive(False)
        self.running = False

    def on_update_status(self):
        if not self.running:
            return False
        statuses = []
        elapsed = (datetime.datetime.now() - self.start_time).seconds or 1
        totalwaiting = 0
        totalpassed = 0
        totaltotal = 0
        graph_maxy = 0
        for i in range(1, size):
            curstatus = None
            comm.send(None, dest=i, tag=messages.STATUS)
            (numwaiting, numpassed, numtotal) = comm.recv(None, source=i, tag=messages.STATUS)

            if matplotlib:
                self.graph_data[i-1] += [numwaiting]
                self.graph_lines[i-1].set_ydata(self.graph_data[i-1])
                self.graph_lines[i-1].set_xdata(range(len(self.graph_data[i-1])))
                totalwaiting += numwaiting
                totalpassed += numpassed
                totaltotal += numtotal
                graph_maxy = max([graph_maxy] + self.graph_data[i-1])

        if matplotlib:
            self.axis.set_ylim(0, int(graph_maxy*1.1))
            self.axis.set_xlim(0, len(self.graph_data[0]))
            self.canvas.draw_idle()

        delta = datetime.datetime.now() - self.start_time
        msg = str(totalwaiting) + " waiting " + \
                str(totalpassed) + " passed " + \
                str(int(float(totaltotal) / elapsed)) + \
                " states/sec " + \
                "Walltime: " + \
                str(delta.seconds) + "." + str(delta.microseconds / 1000)+ \
                " secs"
        self.statusbar.pop(0)
        self.statusbar.push(0, msg)

        return True


    def on_process_mpi(self):
        if not self.running:
            return False
        self.node.termination_detection.master_termination_detection()

        if self.node.termination_detection.terminated:
            self.on_update_status()
            self.on_pause(None)

        if self.node.master_goal_detection():
            self.imgQueryStatus.set_from_stock(gtk.STOCK_YES, 
                gtk.ICON_SIZE_BUTTON)

        return True

# vim:ts=4:sw=4:expandtab
