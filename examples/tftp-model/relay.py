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

dirname = os.path.dirname

sys.path.append(os.path.join(os.path.dirname(sys.path[0]),'base-receiver'))

import relay_receiver
from fuzzm_basic_receiver import FuzzMRatSignal
from relay_receiver import RelayModes
from scapy.all import IP, UDP, Ether, RandShort, sr1


TFTP_PORT = 69
PAYLOAD_LENGTH = 514
OPCODE_LENGTH = 2

UNKNOWN_REQUEST = 0x00
READ_REQUEST = 0x01
WRITE_REQUEST = 0x02
DATA = 0x03
ACK = 0x04
ERROR = 0x05

INITIAL_REQUESTS = [READ_REQUEST, WRITE_REQUEST]
DATA_FLOW = [DATA, ACK, ERROR]


###############################################################################
def fuzzer_resync(fuzz_receiver):
    print("Synchronizing with fuzzer ..")
    while fuzz_receiver.mode == RelayModes.RESYNC:
        time.sleep(0)
    spec = fuzz_receiver.spec
    print("Synchronized.")
    return spec


###############################################################################
def relay(fuzz_ip, target_ip):
    fuzz_receiver = relay_receiver.RelayReceiver(fuzz_ip)

    fuzz_receiver.start()

    spec = fuzzer_resync(fuzz_receiver)

    stream_active = False
    local_port = 0
    remote_port = 0
    local_filter = ""

    while True:
        raw_test_vector = fuzz_receiver.get_next_test_vector()
        test_vector = FuzzMRatSignal(raw_test_vector, spec)

        # print("Relay says keys = %r" % test_vector.keys())
        # print("Relay says vector = " + str(test_vector))

        payload_length = test_vector['payload_length']
        print("Relay says payload_length: %r" % test_vector['payload_length'])
        payload = bytearray(payload_length)

        for index in range(0, payload_length):
            try:
                name = 'msg.payload[' + str(index) + ']'
                byte = int(test_vector[name])
                payload[index] = byte
            except KeyError:
                # print("Relay says out of range payload index: " + str(index))
                pass

        opcode = bytearray(OPCODE_LENGTH)
        try:
            opcode[0] = (int(test_vector['msg.opcode']) >> 8) % 256
            opcode[1] = int(test_vector['msg.opcode']) % 256
            print("Relay says opcode: " +
                  str(test_vector['msg.opcode']) + " (" + str(opcode) + ")")
        except KeyError:
            print("Relay says could not find msg opcode key")
        except:
            print("Unexpected error:", sys.exc_info()[0])
            raise

        if opcode[1] in INITIAL_REQUESTS:
            print("Start new session with opcode %d" % opcode[1])
            stream_active = True
            local_port = RandShort()._fix()
            local_filter = "dst port " + str(local_port)

            pkt = IP(dst=target_ip) / \
                UDP(sport=local_port, dport=TFTP_PORT) / \
                (bytes(opcode) + bytes(payload))

            rx_pkt = sr1(pkt, filter=local_filter, timeout=1,verbose=False)

            remote_port = rx_pkt[0].sport()
        elif stream_active and opcode[1] in DATA_FLOW:
            print("Session data with opcode %d" % opcode[1])
            pkt = IP(dst=target_ip) / \
                UDP(sport=local_port, dport=remote_port) / \
                (bytes(opcode) + bytes(payload))

            sr1(pkt, filter=local_filter, timeout=1,verbose=False)
        else:
            stream_active = False
            print("Opcode %d out of order" % opcode[1])


###############################################################################
def main():
    parser = argparse.ArgumentParser(description="TFTP Relay")
    parser.add_argument('-f', '--fuzz',
                        required=True,
                        help="The address of the fuzzer (AMQP server)")
    parser.add_argument('-t', '--target',
                        required=True,
                        help="The address of the target TFTP server")
    args = parser.parse_args()

    relay(args.fuzz, args.target)


###############################################################################
if __name__ == "__main__":
    sys.exit(main())
