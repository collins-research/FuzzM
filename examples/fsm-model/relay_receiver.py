# 
# Copyright (C) 2017, Rockwell Collins
# All rights reserved.
# 
# This software may be modified and distributed under the terms
# of the 3-clause BSD license.  See the LICENSE file for details.
# 
import collections
import os
import sys
import time

sys.path.append(os.path.abspath("base-receiver"))

from fuzzm_basic_receiver import (FuzzMConfigSpec, FuzzMMsgTypes,
                                  FuzzMRatSignal, FuzzMReceiverBaseClassThread)



class RelayModes:
    RESYNC = "RESYNC"
    RUN = "RUN"
    types = [RESYNC, RUN]


class RelayReceiver(FuzzMReceiverBaseClassThread):

    MAX_QUEUE_LENGTH = 1000

    def __init__(self, host):
        super(RelayReceiver, self).__init__(host)
        self.spec = None
        self.mode = RelayModes.RESYNC
        self.test_vector_queue = collections.deque()

    def callback(self, channel, method, properties, body):
        if self.mode == RelayModes.RESYNC:
            if method.routing_key == FuzzMMsgTypes.CONFIG_SPEC_MSG_TYPE:
                self.spec = FuzzMConfigSpec(body)
                self.mode = RelayModes.RUN
            else:
                pass  # only process the config spec
        elif self.mode == RelayModes.RUN:
            if method.routing_key == FuzzMMsgTypes.TEST_VECTOR_MSG_TYPE:
                if len(self.test_vector_queue) < self.MAX_QUEUE_LENGTH:
                    self.test_vector_queue.append(body)
        else:
            raise Exception("Not implemented")

    def get_next_test_vector(self):
        while len(self.test_vector_queue) < 1:
            time.sleep(0)
        result = self.test_vector_queue.popleft()
        return result
