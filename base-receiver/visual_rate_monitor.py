# 
# Copyright (C) 2017, Rockwell Collins
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
from fuzzm_basic_receiver import FuzzMReceiverBaseClassThread, FuzzMMsgTypes
from pyqtgraph.Qt import QtCore, QtGui

WINDOW_SIZE = 100


class VisualRateReceiver(FuzzMReceiverBaseClassThread):
    def __init__(self, host):
        super(VisualRateReceiver, self).__init__(host)
        self._msg_counts = {}
        for i in FuzzMMsgTypes.types:
            self._msg_counts[i] = collections.deque(maxlen=WINDOW_SIZE + 1)
        self._msg_counts['total'] = collections.deque(maxlen=WINDOW_SIZE + 1)
        for i in list(self._msg_counts.keys()):
            for _ in range(0, WINDOW_SIZE + 1):
                self._msg_counts[i].append(0)
        self._period_start = time.time() // 1

    def callback(self, channel, method, properties, body):
        now = time.time()
        if (now // 1 > self._period_start):
            # print(str(int(now)) + ":" + str(self._msg_counts))
            for i in FuzzMMsgTypes.types:
                self._msg_counts[i].append(0)
            self._msg_counts['total'].append(self._msg_counts['total'][-1])
            self._period_start = now // 1
        self._msg_counts[method.routing_key][-1] += 1
        self._msg_counts['total'][-1] += 1


class App(QtGui.QMainWindow):
    def __init__(self, receiver, parent=None):
        super(App, self).__init__(parent)

        self._receiver = receiver

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
        self.h2.setData(
            np.array(self._receiver._msg_counts[FuzzMMsgTypes.TEST_VECTOR_MSG_TYPE])[:-1])

        self.label.setText(
            'Total: ' + str(self._receiver._msg_counts['total'][-1]))
        QtCore.QTimer.singleShot(100, self._update)


def main():
    parser = argparse.ArgumentParser(description="Run the FuzzM Rate Monitor")
    parser.add_argument('-H', '--host', help="Hostname of the rabbitmq server")
    parser.set_defaults(host='localhost')
    args = parser.parse_args()

    receiver = VisualRateReceiver(args.host)
    receiver.start()
    try:
        app = QtGui.QApplication(sys.argv)
        thisapp = App(receiver)
        thisapp.show()
        app.exec_()

    except KeyboardInterrupt:
        receiver.stop()
        receiver.join()

    receiver.stop()
    receiver.join()


if __name__ == '__main__':
    main()
