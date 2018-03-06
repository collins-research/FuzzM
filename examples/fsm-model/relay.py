#!/usr/bin/env python3
# 
# Copyright (C) 2018, Rockwell Collins
# All rights reserved.
# 
# This software may be modified and distributed under the terms
# of the 3-clause BSD license.  See the LICENSE file for details.
#

import argparse
import os
import socket
import sys
import time

sys.path.append(os.path.join(os.path.dirname(sys.path[0]),'relay-base'))

###############################################################################
from relay_base_class import FuzzMRelayBaseThreadClass

class Relay(FuzzMRelayBaseThreadClass):
    """
    Extend the relay base thread class FuzzMRelayBaseThreadClass.  We
    override the processTestVector() method to perform an appropriate
    action for each new test vector.  In this case we reformat the test
    vector dictionary into a bytearray appropriate for UDP
    transmission to the target.
    """
    def __init__(self, host, target_ip, target_port):
        super(Relay, self).__init__(host)
        self.target_ip = target_ip
        self.target_port = int(target_port)
        self.sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    
    def processTestVector(self,tv):
        """This method is called on every new test vector"""
        msg = formatVector(tv)
        self.sock.sendto(msg, (self.target_ip, self.target_port))

###############################################################################

def formatVector(test_vector):
    """Reformat test vector dictionary into an appropriate target payload"""
    length = int(test_vector['length'])
    if not (0 <= length and length <= 20):
        print("[Relay] Length field out of bounds [0,20] : " + str(length))
        print(test_vector)
        return bytearray(0)
    
    msg = bytearray(length)
    if (0 < length):
        msg[0] = int(test_vector['msg.magic0'])
    if (1 < length):
        msg[1] = int(test_vector['msg.magic1'])
    if (2 < length):
        msg[2] = int(test_vector['msg.seq'])
    if (3 < length):
        msg[3] = int(test_vector['msg.cmd'])
    for index in range(0,length-4):
        name = 'msg.buff[' + str(index) + ']'
        byte = int(test_vector[name])
        msg[4 + index] = byte
    
    return msg


###############################################################################
def main():
    parser = argparse.ArgumentParser(description="FSM Relay")
    parser.add_argument('-a', '--amqp',
                        required=True,
                        help="The address of the AMQP server")
    parser.add_argument('-t', '--target',
                        required=True,
                        help="The target URL")
    parser.add_argument('-p', '--port',
                        required=True,
                        help="The target port")
    args = parser.parse_args()
    
    ## Initialize the fuzzer relay
    fuzz_relay = Relay(args.amqp, args.target, args.port)
    ## Start the relay
    fuzz_relay.start()
    try:
        fuzz_relay.join()
    except KeyboardInterrupt:
        fuzz_relay.stop()
        fuzz_relay.join()
    return 0

###############################################################################
if __name__ == "__main__":
    print("UP AND RUNNINGGGG")
    sys.exit(main())
