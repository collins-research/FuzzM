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
import sys
import time

dirname = os.path.dirname

sys.path.append(os.path.join(os.path.dirname(sys.path[0]),'relay-base'))

from relay_base_class import FuzzMRelayBaseThreadClass
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
class TFTPRelay(FuzzMRelayBaseThreadClass):
    
    def __init__(self,fuzz_ip,target_ip):
        super(TFTPRelay,self).__init__(fuzz_ip,queue_bound=1200)
        self.stream_active = False
        self.target_ip = target_ip
        self.local_port = 0
        self.remote_port = 0
        self.vector = 0
        self.local_filter = ""
    
    def processTestVector(self,test_vector):
        payload_length = test_vector['payload_length']
        print("Relay vector " + str(self.vector) + " at time " + str(time.time() // 1))
        self.vector += 1
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
            self.local_port = RandShort()._fix()
            self.local_filter = "dst port " + str(self.local_port)
            
            pkt = IP(dst=self.target_ip) / \
                UDP(sport=self.local_port, dport=TFTP_PORT) / \
                (bytes(opcode) + bytes(payload))
            
            rx_pkt = sr1(pkt, filter=self.local_filter, timeout=1,verbose=False)
            if rx_pkt:
                self.stream_active = True
                self.remote_port = rx_pkt[0].sport

        elif self.stream_active and opcode[1] in DATA_FLOW:
            print("Session data with opcode %d" % opcode[1])
            pkt = IP(dst=self.target_ip) / \
                UDP(sport=self.local_port, dport=self.remote_port) / \
                (bytes(opcode) + bytes(payload))
            
            sr1(pkt, filter=self.local_filter, timeout=1,verbose=False)
        else:
            self.stream_active = False
            print("Opcode %d out of order" % opcode[1])


###############################################################################
def main():
    parser = argparse.ArgumentParser(description="TFTP Relay")
    parser.add_argument('-a', '--amqp',
                        required=True,
                        help="The address of the AMQP server")
    parser.add_argument('-t', '--target',
                        required=True,
                        help="The address of the target TFTP server")
    args = parser.parse_args()
    relay = TFTPRelay(args.amqp,args.target)
    relay.start()
    try:
        relay.join()
    except KeyboardInterrupt:
        relay.stop()
        relay.join()
    return 0

###############################################################################
if __name__ == "__main__":
    sys.exit(main())
