# 
# Copyright (C) 2017, Rockwell Collins
# All rights reserved.
# 
# This software may be modified and distributed under the terms
# of the 3-clause BSD license.  See the LICENSE file for details.
# 

import argparse
import time

from fuzzm_basic_receiver import FuzzMReceiverBaseClassThread, FuzzMMsgTypes


class RateMonitor(FuzzMReceiverBaseClassThread):

    def __init__(self, host):
        super(RateMonitor, self).__init__(host)
        self._msg_counts = {}
        for i in FuzzMMsgTypes.types:
            self._msg_counts[i] = 0
        self._msg_counts['total'] = 0
        self._period_start = time.time() // 1

    def callback(self, channel, method, properties, body):
        now = time.time()
        if (now // 1 > self._period_start):
            print(str(int(now)) + ":" + str(self._msg_counts))
            for i in FuzzMMsgTypes.types:
                self._msg_counts[i] = 0
            self._period_start = now // 1
        self._msg_counts[method.routing_key] += 1
        self._msg_counts['total'] += 1


def main():
    parser = argparse.ArgumentParser(description="Run the FuzzM Rate Monitor")
    parser.add_argument('-H', '--host', help="Hostname of the rabbitmq server")
    parser.set_defaults(host='localhost')
    args = parser.parse_args()

    receiver = RateMonitor(args.host)
    receiver.start()
    try:
        while receiver.is_alive():
            time.sleep(1)

    except KeyboardInterrupt:
        receiver.stop()
        receiver.join()


if __name__ == '__main__':
    main()
