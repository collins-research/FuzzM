#!/usr/bin/env python3
# 
# Copyright (C) 2018, Rockwell Collins
# All rights reserved.
# 
# This software may be modified and distributed under the terms
# of the 3-clause BSD license.  See the LICENSE file for details.
# 
import argparse

from relay_base_class import (FuzzMBaseThreadClass,FuzzMAMQPInterface,FuzzMLogInterface)

class PrintRelay(FuzzMBaseThreadClass):

    def __init__(self, host, logFile):
        fuzzmInterface = None
        if host:
            fuzzmInterface = FuzzMAMQPInterface(host,logFile=logFile,logSize=100)
        else:
            print("Replaying Log : " + logFile)
            fuzzmInterface = FuzzMLogInterface(logFileName=logFile,queue_bound=10)
        super(PrintRelay, self).__init__(fuzzmInterface)
        self.msg_count = 0
    
    def processTestVector(self,msg):
        report = "Vector {0:10d} : {1:4d}"
        report = report.format(int(msg.seq_id),int(msg.time))
        print(report)
        if self.msg_count == 999:
            self.capture()
            print("Test Vector : " + str(msg))
        self.msg_count += 1
        self.msg_count = self.msg_count % 1000
    
    def processSolution(self,msg):
        report = "Solution {0:10d} : {1:4d}"
        report = report.format(int(msg.seq_id),int(msg.time))
        print(report)
        print("Solution    : " + str(msg))

def main():
    parser = argparse.ArgumentParser(
        description="Run the FuzzM Print Relay")
    parser.add_argument('-A', '--amqp', help="URL of AMQP server")
    parser.set_defaults(amqp='localhost')
    parser.add_argument('-L', '--logfile', help="Logfile name")
    parser.set_defaults(logfile=None)
    args = parser.parse_args()

    relay = PrintRelay(args.amqp,args.logfile)
    relay.start()
    try:
        relay.join()
    except KeyboardInterrupt:
        relay.stop()
        relay.join()

if __name__ == '__main__':
    main()
