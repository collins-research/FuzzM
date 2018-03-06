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

from relay_base_class import (FuzzMRelayBaseThreadClass)

class PrintRelay(FuzzMRelayBaseThreadClass):

    def __init__(self, host):
        super(PrintRelay, self).__init__(host,queue_bound=100)
    
    def processTestVector(self,msg):
        print("Test Vector " + str(time.time() // 1))
        time.sleep(1)

def main():
    parser = argparse.ArgumentParser(
        description="Run the Slow Relay")
    parser.add_argument('-a', '--amqp', help="URL of AMQP server")
    parser.set_defaults(amqp='localhost')
    args = parser.parse_args()

    relay = PrintRelay(args.amqp)
    relay.start()
    try:
        relay.join()
    except KeyboardInterrupt:
        relay.stop()
        relay.join()

if __name__ == '__main__':
    main()
