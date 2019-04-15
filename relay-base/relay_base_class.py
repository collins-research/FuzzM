#!/usr/bin/env python3
# 
# Copyright (C) 2018, Rockwell Collins
# All rights reserved.
# 
# This software may be modified and distributed under the terms
# of the 3-clause BSD license.  See the LICENSE file for details.
# 
import lzma 
import argparse
import collections
import threading
import pika
import os
from fractions import Fraction
from datetime import datetime

class FuzzMMsgTypes:
    TEST_VECTOR_MSG_TYPE = "TEST_VECTOR_MSG_TYPE"
    COUNTER_EXAMPLE_MSG_TYPE = "COUNTER_EXAMPLE_MSG_TYPE"
    CONFIG_SPEC_MSG_TYPE = "CONFIG_SPEC_MSG_TYPE"
    types = [TEST_VECTOR_MSG_TYPE,
             COUNTER_EXAMPLE_MSG_TYPE, CONFIG_SPEC_MSG_TYPE]

class FieldIndexType:
    def __init__(self,findex,ftype):
        self.findex = findex
        self.ftype  = ftype

## The current vector message format is:
##   vector := "TAG SEQ TIME [VALUE]* "
## The current spec message format is:
##   spec   := "TAG [NAME TYPE]* "
class MessageFormat:
    VectorPreludeSize        = 3
    SpecificationPreludeSize = 1

class FuzzMConfigSpec(dict):
    def __init__(self, spec_entries):
        super(FuzzMConfigSpec, self).__init__()
        spec_size = len(spec_entries)
        assert(spec_size >= MessageFormat.SpecificationPreludeSize)
        assert(((spec_size - MessageFormat.SpecificationPreludeSize) % 2) == 0)
        index = MessageFormat.VectorPreludeSize
        assert(spec_entries[0] == FuzzMMsgTypes.CONFIG_SPEC_MSG_TYPE)
        for i in range(MessageFormat.SpecificationPreludeSize, len(spec_entries), 2):
            self[spec_entries[i]] = FieldIndexType(index,spec_entries[i + 1])
            index += 1

class FuzzMRatSignal(dict):
    def __init__(self, data, spec):
        super(FuzzMRatSignal, self).__init__()
        assert(len(data) >= MessageFormat.VectorPreludeSize)
        tag         =     data[0]
        self.seq_id = int(data[1])
        self.time   = int(data[2])
        assert((tag == FuzzMMsgTypes.TEST_VECTOR_MSG_TYPE) or (tag == FuzzMMsgTypes.COUNTER_EXAMPLE_MSG_TYPE))
        for field in list(spec.keys()):
            if spec[field].ftype == 'int':
                self[field] = int(data[spec[field].findex])
            elif spec[field].ftype == 'bool':
                val = data[spec[field].findex]
                if val not in ['0', '1']:
                    raise Exception("Invalid boolean value: " + val)
                self[field] = (val == '1')
            elif spec[field].ftype == 'real':
                self[field] = Fraction(data[spec[field].findex])
            else:
                raise Exception("Unhanded type: " + spec['field'].ftype)

class FlowControlState:
    PAUSED = 0
    RUNNING = 1

class FlowControl:
    def __init__(self):
        self.state = FlowControlState.PAUSED
    def isPaused(self):
        return self.state == FlowControlState.PAUSED
    def resume(self):
        print("Flow Control : Resume")
        self.state = FlowControlState.RUNNING
    def pause(self):
        print("Flow Control : Pause")
        self.state = FlowControlState.PAUSED
    def close(self):
        self.state = FlowControlState.PAUSED

class LOGFlowControl(FlowControl):
    def __init__(self):
        super(LOGFlowControl,self).__init__()
        self.condition = threading.Condition(threading.Lock())
    def pause(self):
        if not self.isPaused():
            with self.condition:
                super(LOGFlowControl,self).pause()
                self.condition.wait()
    def resume(self):
        if self.isPaused():
            with self.condition:
                super(LOGFlowControl,self).resume()
                self.condition.notify()

class Logger:
    def __init__(self,enabled=False,logFile="FuzzM",logSize=1000000):
        self.enabled = enabled
        self.logSize = logSize/2
        self.logFile = logFile
        self.logFileInc = 0
        self.entries = 0
        self.nextLogger = None
        self.specData = None
        self.currLogger = self.newLogFile() if enabled else None
    def newLogFile(self):
        if not self.enabled:
            return None
        self.entries = 0
        clock = datetime.today()
        logFileName = self.logFile
        logFileName += "-" + str(clock.year)
        logFileName += "-" + str(clock.month)
        logFileName += "-" + str(clock.day)
        logFileName += "-" + str(clock.hour)
        logFileName += "-" + str(clock.minute)
        logFileName += "-" + str(self.logFileInc)
        logFileName += ".log.gz"
        self.logFileInc += 1
        file = lzma.open(logFileName,'ab')
        if self.specData:
            file.write(self.specData + b"\n")
        ##print("Creating  Logfile : " + file._fp.name)
        ##assert(not file.closed)
        return file
    def retire(self,ofile,delete=True):
        name = ofile._fp.name
        ##action = "Removing " if delete else "Saving   "
        ##print(action + " Logfile : " + name + " (" + str(self.entries) + ")")
        ofile.close()
        if delete:
            os.remove(name)
    def rollOver(self):
        if not self.enabled:
            return
        print("Rotating  LogFile ...")
        if self.nextLogger:
            self.retire(self.currLogger)
            self.currLogger = self.nextLogger
        self.nextLogger = self.newLogFile()
        ##assert(not self.currLogger.closed)
        ##print("Done.")
    def capture(self):
        if not self.enabled:
            return
        print("Capturing LogFile : " + self.currLogger._fp.name)
        self.retire(self.currLogger,delete=False)
        self.currLogger = self.newLogFile()
        if self.nextLogger:
            self.retire(self.nextLogger)
        self.nextLogger = None
        ##assert(not self.currLogger.closed)
        ##print("Done.")
    def write(self,data,spec=False):
        if not self.enabled:
            return
        if spec:
            self.specData = data
        if not self.specData:
            return
        if (self.entries >= self.logSize):
            self.rollOver()
        self.currLogger.write(data + b"\n")
        if self.nextLogger:
            self.nextLogger.write(data + b"\n")
        self.entries += 1
        ##assert(not self.currLogger.closed)
    def close(self):
        if not self.enabled:
            return
        self.retire(self.currLogger)
        if self.nextLogger:
            self.retire(self.nextLogger)
        self.enabled = False

class AMQPFlowControl(FlowControl):
    
    def __init__(self,host,exchange):
        super(AMQPFlowControl,self).__init__()
        self.host = host
        self.flow_ctrl_exchange_name = exchange + "_FLOW_CTRL"
        self.connect()
        self.resume()
    
    def connect(self):
        self.flow_ctrl_connection = pika.BlockingConnection(
            pika.ConnectionParameters(host=self.host))
        self.flow_ctrl_channel = self.flow_ctrl_connection.channel()
        self.flow_ctrl_channel.exchange_declare(
            exchange=self.flow_ctrl_exchange_name, exchange_type='direct')
    
    def resume(self):
        while self.isPaused():
            try:
                self.flow_ctrl_channel.basic_publish(
                    exchange=self.flow_ctrl_exchange_name,
                    routing_key="FLOW_CTRL",
                    body="RESUME")
                break
            except pika.exceptions.ConnectionClosed:
                print("Resetting Connection to " + self.flow_ctrl_exchange_name)
                self.connect()
        super(AMQPFlowControl,self).resume()
    
    def pause(self):
        while not self.isPaused():
            try:
                self.flow_ctrl_channel.basic_publish(
                    exchange=self.flow_ctrl_exchange_name,
                    routing_key="FLOW_CTRL",
                    body="PAUSE")
                break
            except pika.exceptions.ConnectionClosed:
                print("Resetting Connection to " + self.flow_ctrl_exchange_name)
                self.connect()
        super(AMQPFlowControl,self).pause()
    
    def close(self):
        super(AMQPFlowControl,self).close()
        try:
            self.flow_ctrl_channel.close()
        except:
            pass
        try:
            self.flow_ctrl_connection.close()
        except:
            pass

class FlowControlQueue():
    
    def __init__(self, flowControl, queue_bound=10000):
        self.condition = threading.Condition(threading.Lock())
        self.queue_hi_water_mark = queue_bound
        self.queue_lo_water_mark = queue_bound/2
        self.msg_queue = collections.deque()
        self.flowControl = flowControl
    
    def put(self, item):
        with self.condition:
            self.msg_queue.append(item)
            self.condition.notify()
        if (not self.flowControl.isPaused()) and len(self.msg_queue) > self.queue_hi_water_mark:
            self.flowControl.pause()
    
    def get(self,timeout_sec=1.0):
        item = None
        with self.condition:
            if self.flowControl.isPaused() and len(self.msg_queue) < self.queue_lo_water_mark:
                self.flowControl.resume()
            if len(self.msg_queue) <= 0:
                ## print("Flow Control Queue : Waiting ..")
                self.condition.wait(timeout_sec)
            if len(self.msg_queue) > 0:
                ## print("Flow Control Queue Depth " + str(len(self.msg_queue)))
                item = self.msg_queue.popleft()
        return item
    
    def isFull(self):
        return len(self.msg_queue) > self.queue_hi_water_mark
    
    def isEmpty(self):
        return len(self.msg_queue) == 0
    
    def close(self):
        try:
            self.flowControl.close()
        except:
            pass

class FuzzMInterface():
    
    def __init__(self,fcQueue):
        self.fcQueue = fcQueue
        self.spec = None
    
    def processMessage(self,vlist):
        key = vlist[0]
        if (key == FuzzMMsgTypes.CONFIG_SPEC_MSG_TYPE):
            self.spec = FuzzMConfigSpec(vlist)
            self.put((key,self.spec))
        elif (key == FuzzMMsgTypes.TEST_VECTOR_MSG_TYPE) or (key == FuzzMMsgTypes.COUNTER_EXAMPLE_MSG_TYPE):
            if self.spec:
                msg = FuzzMRatSignal(vlist, self.spec)
                self.put((key,msg))
        else:
            assert(False)
    
    def put(self,pair):
        self.fcQueue.put(pair)
    
    def get(self,timeout_sec=1.0):
        return self.fcQueue.get(timeout_sec)
    
    def close(self):
        self.fcQueue.close()
    
    def capture(self):
        Pass
    
    def consumeInputs(self):
        raise Exception('consumeInputs() method must be overriden')

class FuzzMLogInterface(FuzzMInterface):
    
    def __init__(self,logFileName,queue_bound=10000):
        LOGfc = LOGFlowControl()
        fcQueue = FlowControlQueue(LOGfc,queue_bound=queue_bound)
        super(FuzzMLogInterface,self).__init__(fcQueue)
        self.file = lzma.open(logFileName,'rb')
    
    def consumeInputs(self):
        while not self.fcQueue.isFull():
            payload = self.file.readline()
            if not payload:
                raise Exception("File Empty")
            vlist = payload.decode('utf-8').split()
            self.processMessage(vlist)
    
    def close(self):
        super(FuzzMLogInterface,self).close()
        self.file.close()

class FuzzMAMQPInterface(FuzzMInterface):
    
    def __init__(self,host,exchange="fuzzm-output-engine",queue_bound=10000,logFile=None,logSize=1000000):
        AMQPfc = AMQPFlowControl(host,exchange)
        fcQueue = FlowControlQueue(AMQPfc,queue_bound=queue_bound)
        super(FuzzMAMQPInterface,self).__init__(fcQueue)
        logEnabled = True if logFile else False
        self.logger = Logger(enabled=logEnabled,logFile=logFile,logSize=logSize)
        self.exchange_name = exchange
        self.params = pika.ConnectionParameters(host=host)
        self.connect()
        self.condition = threading.Condition(threading.Lock())
    
    def connect(self):
        self.connection = pika.BlockingConnection(self.params)
        self.channel = self.connection.channel()
        self.channel.exchange_declare(
            exchange=self.exchange_name, exchange_type='direct')
        result = self.channel.queue_declare(queue='channel_queue',exclusive=True)
        self.queue_name = result.method.queue
        self.channel.queue_bind(exchange=self.exchange_name,
                                 queue=self.queue_name,
                                 routing_key=str(FuzzMMsgTypes.TEST_VECTOR_MSG_TYPE))
        self.channel.queue_bind(exchange=self.exchange_name,
                                 queue=self.queue_name,
                                 routing_key=str(FuzzMMsgTypes.COUNTER_EXAMPLE_MSG_TYPE))
        self.channel.queue_bind(exchange=self.exchange_name,
                                 queue=self.queue_name,
                                 routing_key=str(FuzzMMsgTypes.CONFIG_SPEC_MSG_TYPE))
        
        self.channel.basic_consume(on_message_callback=self.amqp_callback, queue=self.queue_name)
                                   
    
    def amqp_callback(self, channel, method, properties, body):
        keybytes = (method.routing_key + " ").encode('utf-8')
        payload = keybytes + body
        with self.condition:
            self.logger.write(payload,spec=(method.routing_key == FuzzMMsgTypes.CONFIG_SPEC_MSG_TYPE))
        vlist = payload.decode('utf-8').split()
        self.processMessage(vlist)
    
    def capture(self):
        with self.condition:
            self.logger.capture()
    
    def consumeInputs(self):
        while True:
            try:
                self.channel.connection.process_data_events(1)
                break
            except pika.exceptions.ConnectionClosed:
                print("Resetting Connection to " + self.exchange_name)
                self.connect()
    
    def close(self):
        super(FuzzMAMQPInterface,self).close()
        self.logger.close()
        self.channel.close()
        self.connection.close()

class Producer(threading.Thread):
    
    def __init__(self,amqp):
        super(Producer,self).__init__()
        self.amqp = amqp
        self.stop_event = threading.Event()
    
    def run(self):
        super(Producer,self).run()
        try:
            while not self.stoppingEvent():
                self.amqp.consumeInputs()
        except:
            pass
    
    def reset(self):
        self.stop()
    
    def stoppingEvent(self):
        return self.stop_event.is_set()
    
    def stop(self):
        self.stop_event.set()

## Now this is the same for both AMQP and LOG as producers ..
## .. but the amqp must perform message decoding.
class FuzzMBaseThreadClass(threading.Thread):
    ''' RelayBaseThreadClass is a base thread class every relay should extend to interface with FuzzM.
        Each child class should override the processTestVector() and processSolution() methods.'''
    
    def __init__(self,fuzzmInterface):
        super(FuzzMBaseThreadClass,self).__init__()
        self.fuzzmInterface = fuzzmInterface
        self.producer   = Producer(self.fuzzmInterface)
        self.stop_event = threading.Event()
    
    def stoppingEvent(self):
        return self.stop_event.is_set()
    
    def start(self):
        self.producer.start()
        super(FuzzMBaseThreadClass,self).start()
    
    def reset(self):
        self.stop()
    
    def stop(self):
        self.producer.stop()
        self.stop_event.set()
    
    def run(self):
        try:
            while not self.stoppingEvent():
                if (not self.producer.isAlive()) and self.fuzzmInterface.fcQueue.isEmpty():
                    break
                item = self.fuzzmInterface.get(timeout_sec=1.0)
                if not item:
                    continue
                (key,msg) = item
                if key == FuzzMMsgTypes.CONFIG_SPEC_MSG_TYPE:
                    self.processSpec(msg)
                elif key == FuzzMMsgTypes.TEST_VECTOR_MSG_TYPE:
                    self.processTestVector(msg)
                elif key == FuzzMMsgTypes.COUNTER_EXAMPLE_MSG_TYPE:
                    self.processSolution(msg)
                else:
                    raise Exception("Unexpected Routing Key : " + key)
        finally:
            self.producer.stop()
            self.producer.join()
            self.fuzzmInterface.close()
    
    def capture(self):
        self.fuzzmInterface.capture()
    
    def processSpec(self,msg):
        '''processSpec() is called every time a vector specification is received from FuzzM.'''
        pass
    
    def processTestVector(self,msg):
        '''processTestVector() is called on every vector received from FuzzM.'''
        raise Exception("The processTestVector() method should be overwritten by the inheriting class.")
    
    def processSolution(self,msg):
        '''processSolution() is called on every counter example received from FuzzM.'''
        pass

class FuzzMRelayBaseThreadClass(FuzzMBaseThreadClass):
    """
    A base class for an AMQP relay.
    """    
    def __init__(self,host,exchange="fuzzm-output-engine",queue_bound=10000,logFile=None,logSize=1000000):
        super(FuzzMRelayBaseThreadClass,self).__init__(FuzzMAMQPInterface(host,exchange=exchange,queue_bound=queue_bound,logFile=logFile,logSize=logSize))

class FuzzMReplayBaseThreadClass(FuzzMBaseThreadClass):
    """
    A base class for Logfile replay.
    """
    def __init__(self,logFileName,queue_bound=10000):
        super(FuzzMReplayBaseThreadClass,self).__init__(FuzzMLogInterface(logFileName=logFileName,queue_bound=queue_bound))

def main():
    # This is for development and testing purposes and should not be used directly
    parser = argparse.ArgumentParser(description="Run the FuzzM Relay")
    parser.add_argument('-a', '--amqp', help="URL of AMQP server")
    parser.set_defaults(amqp='localhost')
    args = parser.parse_args()
    amqp = args.amqp
    relay = FuzzMRelayBaseThreadClass(amqp,exchange="fuzzm-output-engine",logFile="FuzzM")
    relay.start()
    relay.join(10.0)
    relay.stop()
    relay.join()
    print("DONE")

if __name__ == '__main__':
    main()
    
