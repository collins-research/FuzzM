# 
# Copyright (C) 2017, Rockwell Collins
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

sys.path.append(os.path.join(os.path.dirname(sys.path[0]),'base-receiver'))

from fuzzm_basic_receiver import (FuzzMConfigSpec, FuzzMMsgTypes,
                                  FuzzMRatSignal, FuzzMReceiverBaseClassThread)



###############################################################################
class RelayModes:
    RESYNC = "RESYNC"
    RUN = "RUN"
    types = [RESYNC, RUN]

###############################################################################
class RelayReceiver(FuzzMReceiverBaseClassThread):

    def __init__(self, host, target_ip, target_port):
        super(RelayReceiver, self).__init__(host)
        self.spec = None
        self.target_ip = target_ip
        self.target_port = int(target_port)
        self.mode = RelayModes.RESYNC
        self.sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)

    def callback(self, channel, method, properties, body):
        if self.mode == RelayModes.RESYNC:
            if method.routing_key == FuzzMMsgTypes.CONFIG_SPEC_MSG_TYPE:
                self.spec = FuzzMConfigSpec(body)
                self.mode = RelayModes.RUN
            else:
                pass  # only process the config spec
        elif self.mode == RelayModes.RUN:
            if method.routing_key == FuzzMMsgTypes.TEST_VECTOR_MSG_TYPE:
                ## Get the next test vector ..
                msg = nextMessage(body, self.spec)
                ## Send it to the target.
                self.sock.sendto(msg, (self.target_ip, self.target_port))
        else:
            raise Exception("Not implemented")


###############################################################################
def fuzzer_resync(fuzz_receiver):
    print("Synchronizing with fuzzer ..")
    while fuzz_receiver.mode == RelayModes.RESYNC:
        time.sleep(0)
    print("Synchronized.")


###############################################################################
def nextMessage(raw_test_vector, spec):
    test_vector = FuzzMRatSignal(raw_test_vector, spec)

    ## print("[Relay] vector = {0:08d}:{1:03d}".format(test_vector.seq_id,test_vector.time))

    ## Reformat dictionary into appropriate target payload ..
    length = int(test_vector['length'])
    if not (0 <= length and length < 32):
        print("[Relay] Length field out of bounds [0,32] : " + str(length))
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

    ## Initialize the base receiver
    fuzz_receiver = RelayReceiver(args.fuzz, args.target_ip, args.target_port)
    ## Start the receiver
    fuzz_receiver.start()
    ## Synchronize with the fuzzer
    fuzzer_resync(fuzz_receiver)

    while fuzz_receiver.is_alive():
        try:
            time.sleep(1)
        except KeyboardInterrupt:
            fuzz_receiver.stop()
            fuzz_receiver.join()
            break


###############################################################################
if __name__ == "__main__":
    print("UP AND RUNNINGGGG")
    sys.exit(main())
