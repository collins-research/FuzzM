#!/usr/bin/env python3
# 
# Copyright (C) 2018, Rockwell Collins
# All rights reserved.
# 
# This software may be modified and distributed under the terms
# of the 3-clause BSD license.  See the LICENSE file for details.
# 

import argparse
import time

from relay_base_class import FuzzMRelayBaseThreadClass

class RateMonitor(FuzzMRelayBaseThreadClass):
    
    def __init__(self, host):
        super(RateMonitor, self).__init__(host)
        self.period_start = time.time() // 1
        self.vectors = 0
        self.average_vectors = 0.0
        self.solutions = 0
        self.average_solutions_c = 0.0
    
    def doPrint(self):
        now = time.time() // 1
        if (now > self.period_start):
            self.average_vectors     = (9.0*self.average_vectors + self.vectors)/10.0
            self.average_solutions_c = (9.0*self.average_solutions_c + 100*self.solutions)/10.0
            av_vec = self.average_vectors
            av_sln = int(self.average_solutions_c)/100.0
            report = "{0:10d}  |  vectors: {1:5d} / {2: 7.1f}  |  solutions: {3:2d} / {4: 5.2f}"
            report = report.format(int(now),self.vectors,av_vec,self.solutions,av_sln)
            print(report)
            self.period_start = now
            self.vectors = 0
            self.solutions = 0
    
    def processTestVector(self,msg):
        self.vectors += 1
        self.doPrint()
    
    def processSolution(self,msg):
        self.solutions += 1
        self.doPrint()


def main():
    parser = argparse.ArgumentParser(description="Run the FuzzM Rate Monitor")
    parser.add_argument('-a', '--amqp', help="URL of AMQP server")
    parser.set_defaults(amqp='localhost')
    args = parser.parse_args()

    relay = RateMonitor(args.amqp)
    relay.start()
    try:
        relay.join()
    except KeyboardInterrupt:
        relay.stop()
        relay.join()

if __name__ == '__main__':
    main()
