#!/usr/bin/python3
"""Top-level monitor script for FSM Demo"""

import subprocess
import sys
import psutil
import os
from threading import Thread
from time import sleep

PROCESS_NAME = 'fsm'
PROCESS_COMMAND = './start.sh'


###############################################################################
class MonitorThread(Thread):
    """ Monitor the process"""
    def __init__(self):
        Thread.__init__(self)
        self.running = True

    def find_process(self):
        """ Search for process by name """
        found = False
        for proc in psutil.process_iter(attrs=['name']):
            if proc.info['name'] == PROCESS_NAME:
                found = True

        return found

    def run(self):
        """ The thread function """
        while self.running is True:
            found = self.find_process()

            if not found and self.running is True:
                print("(Re)Starting process")
                subprocess.Popen([PROCESS_COMMAND])

                while not found:
                    found = self.find_process()
            else:
                sleep(1)

    def stop(self):
        """ Stop execution """
        self.running = False


###############################################################################
def main():
    """ Main function """
    monitor = MonitorThread()
    monitor.start()

    try:
        while True:
            sleep(1)
    except KeyboardInterrupt:
        print("Stopping")
        monitor.stop()
        monitor.join()


###############################################################################
if __name__ == "__main__":
    sys.exit(main())
