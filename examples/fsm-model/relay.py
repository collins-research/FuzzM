# 
# Copyright (C) 2017, Rockwell Collins
# All rights reserved.
# 
# This software may be modified and distributed under the terms
# of the 3-clause BSD license.  See the LICENSE file for details.
# 
import argparse
import os
import sys
import time

sys.path.append(os.path.join(os.path.dirname(sys.path[0]),'base-receiver'))

import relay_receiver
from fuzzm_basic_receiver import FuzzMRatSignal
from relay_receiver import RelayModes
from scapy.all import IP, UDP, Ether, Raw, send


###############################################################################
def fuzzer_resync(fuzz_receiver):
    print("Synchronizing with fuzzer ..")
    while fuzz_receiver.mode == RelayModes.RESYNC:
        time.sleep(0)
    spec = fuzz_receiver.spec
    print("Synchronized.")
    return spec

###############################################################################
def nextMessage(fuzz_receiver, spec):
    msg = bytearray(0)
    while True:
        ## Get a vector from the fuzzer ..
        raw_test_vector = fuzz_receiver.get_next_test_vector()
        ## Represent it as a dictionary ..
        test_vector = FuzzMRatSignal(raw_test_vector, spec)
        
        # print("[Relay] vector = " + str(test_vector))
        
        ## Reformat dictionary into appropriate target payload ..
        try:
            length = int(test_vector['length'])
            if not (0 <= length and length < 32):
                print("[Relay] Length field out of bounds [0,32] : " + str(length))
                print(test_vector)
                continue
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
        except KeyError:
            print("[Relay] Key Error Accessing Message :")
            print(test_vector)
            continue
        break
    return msg

###############################################################################
def relay(fuzz_ip, target_ip, target_port):
    ## Initialize the base receiver
    fuzz_receiver = relay_receiver.RelayReceiver(fuzz_ip)
    ## Start the receiver
    fuzz_receiver.start()
    ## Synchronize with the fuzzer
    spec = fuzzer_resync(fuzz_receiver)
    
    ## Forever ..
    while True:
        ## Get the next test vector ..
        msg = nextMessage(fuzz_receiver, spec)
        ## Reformat it ..
        pkt = IP(dst=target_ip)/UDP(dport=int(target_port))/Raw(load=bytes(msg))
        ## Send it to the target.
        send(pkt)


###############################################################################
def main():
    parser = argparse.ArgumentParser(description="FSM Relay")
    parser.add_argument('-f', '--fuzz',
                        required=True,
                        help="The address of the fuzzer (AMQP server)")
    parser.add_argument('-ti', '--target_ip',
                        required=True,
                        help="The target IP")
    parser.add_argument('-tp', '--target_port',
                        required=True,
                        help="The target port")
    args = parser.parse_args()

    relay(args.fuzz, args.target_ip, args.target_port)


###############################################################################
if __name__ == "__main__":
    print("UP AND RUNNINGGGG")
    sys.exit(main())
