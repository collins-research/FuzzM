# 
# Copyright (C) 2017, Rockwell Collins
# All rights reserved.
# 
# This software may be modified and distributed under the terms
# of the 3-clause BSD license.  See the LICENSE file for details.
# 
import argparse
import collections
import threading

import pika


class FuzzMMsgTypes:
    TEST_VECTOR_MSG_TYPE = "TEST_VECTOR_MSG_TYPE"
    COUNTER_EXAMPLE_MSG_TYPE = "COUNTER_EXAMPLE_MSG_TYPE"
    CONFIG_SPEC_MSG_TYPE = "CONFIG_SPEC_MSG_TYPE"
    types = [TEST_VECTOR_MSG_TYPE,
             COUNTER_EXAMPLE_MSG_TYPE, CONFIG_SPEC_MSG_TYPE]


class FuzzMConfigSpec(dict):
    def __init__(self, msg):
        super(FuzzMConfigSpec, self).__init__()
        spec_entries = msg.decode('utf-8').split()
        index = 2
        for i in range(0, len(spec_entries), 2):
            self[spec_entries[i]] = {}
            self[spec_entries[i]]['index'] = index
            self[spec_entries[i]]['type'] = spec_entries[i + 1]
            index += 1


class FuzzMRatSignal(dict):
    def __init__(self, msg, spec):
        super(FuzzMRatSignal, self).__init__()
        data = msg.decode('utf-8').split()
        self.seq_id = int(data[0])
        self.time = int(data[1])
        for field in list(spec.keys()):
            if spec[field]['type'] == 'int':
                self[field] = int(data[spec[field]['index']])
            elif spec[field]['type'] == 'bool':
                val = data[spec[field]['index']]
                if val not in ['0', '1']:
                    raise Exception("Invalid boolean value: " + val)
                self[field] = (val == '1')
            else:
                raise Exception("Unhanded type: " + spec['field']['type'])


class FuzzMReceiverBaseClassThread(threading.Thread):
    ''' FuzzMReceiverBaseClassThread is a base class that should be inherited from to receive FuzzM output messages.
        Each child class should override the callback function to perform the specific message processing. '''

    def __init__(self, host):
        super(FuzzMReceiverBaseClassThread, self).__init__()
        self._stop_event = threading.Event()

        self._exchange_name = "fuzzm-output-engine"
        self._connection = pika.BlockingConnection(
            pika.ConnectionParameters(host=host))
        self._channel = self._connection.channel()
        self._channel.exchange_declare(
            exchange=self._exchange_name, exchange_type='direct')
        result = self._channel.queue_declare(exclusive=True)
        self._queue_name = result.method.queue
        self._channel.queue_bind(exchange=self._exchange_name,
                                 queue=self._queue_name,
                                 routing_key=str(FuzzMMsgTypes.TEST_VECTOR_MSG_TYPE))
        self._channel.queue_bind(exchange=self._exchange_name,
                                 queue=self._queue_name,
                                 routing_key=str(FuzzMMsgTypes.COUNTER_EXAMPLE_MSG_TYPE))
        self._channel.queue_bind(exchange=self._exchange_name,
                                 queue=self._queue_name,
                                 routing_key=str(FuzzMMsgTypes.CONFIG_SPEC_MSG_TYPE))

        self._channel.basic_consume(self.callback, queue=self._queue_name,
                                    no_ack=True)

    def callback(self, channel, method, properties, body):
        ''' The callback function is called when a message is received from FuzzM.

        - method.routing_key specifies the type of message received
        - body contains the actual message

        - For further information reference the pika documentation
        '''
        print((" [x] Received %r" % body) + ("; %r" % method.routing_key))
        raise Exception(
            "The callback function should be overwritten by the inheriting class.")

    def run(self):
        super(FuzzMReceiverBaseClassThread, self).run()
        try:
            while not self._stop_event.is_set():
                self._channel.connection.process_data_events(1)
        finally:
            self._stop_event.set()
        self._channel.close()
        self._connection.close()

    def reset(self):
        self.stop()

    def stop(self):
        self._stop_event.set()


def main():
    # This is for development and testing purposes and should not be used directly
    parser = argparse.ArgumentParser(description="Run the FuzzM Receiver")
    parser.add_argument('-H', '--host', help="Hostname of the rabbitmq server")
    parser.set_defaults(host='localhost')
    args = parser.parse_args()

    receiver = FuzzMReceiverBaseClassThread(args.host)
    receiver.start()

    receiver.join(150)
    receiver.stop()
    receiver.join()
    print("DONE")


if __name__ == '__main__':
    main()
