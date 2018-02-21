# 
# Copyright (C) 2017, Rockwell Collins
# All rights reserved.
# 
# This software may be modified and distributed under the terms
# of the 3-clause BSD license.  See the LICENSE file for details.
# 
import argparse
import time

from fuzzm_basic_receiver import (FuzzMReceiverBaseClassThread,
                                  FuzzMConfigSpec, FuzzMMsgTypes,
                                  FuzzMRatSignal)


class PrintReceiver(FuzzMReceiverBaseClassThread):

    def __init__(self, host):
        super(PrintReceiver, self).__init__(host)
        self._msg_counts = {}
        self._msg_count_mod = {}
        for i in FuzzMMsgTypes.types:
            self._msg_counts[i] = 0
            self._msg_count_mod[i] = 10
        self._msg_count_mod[FuzzMMsgTypes.TEST_VECTOR_MSG_TYPE] = 1000
        self._spec = None

    def callback(self, channel, method, properties, body):
        if self._msg_counts[method.routing_key] % self._msg_count_mod[method.routing_key] == 0:
            if method.routing_key == FuzzMMsgTypes.CONFIG_SPEC_MSG_TYPE:
                self._spec = FuzzMConfigSpec(body)
                print("Received " + method.routing_key +
                      " message: " + str(self._spec))
            else:
                if self._spec is not None:
                    rat_signal = FuzzMRatSignal(body, self._spec)
                    print("Received " + method.routing_key + " message: seq_id(" + str(rat_signal.seq_id) +
                          ") time(" + str(rat_signal.time) + ") " + str(rat_signal))
                else:
                    print("Received " + method.routing_key +
                          " message: " + str(body))
        self._msg_counts[method.routing_key] += 1


def main():
    parser = argparse.ArgumentParser(
        description="Run the FuzzM Print Receiver")
    parser.add_argument('-H', '--host', help="Hostname of the rabbitmq server")
    parser.set_defaults(host='localhost')
    args = parser.parse_args()

    receiver = PrintReceiver(args.host)
    receiver.start()

    try:
        while receiver.is_alive():
            time.sleep(1)
    except KeyboardInterrupt:
        receiver.stop()
        receiver.join()


if __name__ == '__main__':
    main()
