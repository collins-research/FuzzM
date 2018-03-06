#!/usr/bin/env python3
# 
# Copyright (C) 2018, Rockwell Collins
# All rights reserved.
# 
# This software may be modified and distributed under the terms
# of the 3-clause BSD license.  See the LICENSE file for details.
# 
import argparse
import collections
import sys
import time

import numpy as np
import pyqtgraph as pg
from relay_base_class import FuzzMRelayBaseThreadClass
from pyqtgraph.Qt import QtCore, QtGui

WINDOW_SIZE = 100


class VisualRateMonitor(FuzzMRelayBaseThreadClass):
    
    def __init__(self, host):
        super(VisualRateMonitor, self).__init__(host)
        self.vectors = collections.deque(maxlen=WINDOW_SIZE + 1)
        self.total = 0.0
        for _ in range(0, WINDOW_SIZE + 1):
            self.vectors.append(0.0)
        self.period_start = time.time() // 1
    
    def processTestVector(self,msg):
        now = time.time() // 1
        if (now > self.period_start):
            self.vectors.append(0.0)
            self.period_start = now
        self.vectors[-1] += 1.0
        self.total += 1.0


class App(QtGui.QMainWindow):
    
    def __init__(self, relay, parent=None):
        super(App, self).__init__(parent)

        self._relay = relay

        #### Create Gui Elements ###########
        self.mainbox = QtGui.QWidget()
        self.setCentralWidget(self.mainbox)
        self.mainbox.setLayout(QtGui.QVBoxLayout())

        self.canvas = pg.GraphicsLayoutWidget()
        self.mainbox.layout().addWidget(self.canvas)

        self.label = QtGui.QLabel()
        self.mainbox.layout().addWidget(self.label)

        #  line plot
        self.plot = self.canvas.addPlot()
        self.h2 = self.plot.plot(pen='y')

        #### Start  #####################
        self._update()

    def _update(self):
        self.h2.setData(np.array(self._relay.vectors))
        self.label.setText('Total : ' + str(self._relay.total))
        QtCore.QTimer.singleShot(100, self._update)


def main():
    parser = argparse.ArgumentParser(description="Run the FuzzM Rate Monitor")
    parser.add_argument('-a', '--amqp', help="URL of AMQP server")
    parser.set_defaults(amqp='localhost')
    args = parser.parse_args()

    relay = VisualRateMonitor(args.amqp)
    relay.start()
    try:
        app = QtGui.QApplication(sys.argv)
        thisapp = App(relay)
        thisapp.show()
        app.exec_()
    finally:
        relay.stop()
        relay.join()

if __name__ == '__main__':
    main()
