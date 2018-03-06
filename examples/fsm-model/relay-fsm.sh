#! /bin/bash
umask 000
chmod a+rw *.py
chmod a+rw /root/relay-base/*.py
rm -rf __pycache__
rm -rf /root/relay-base/__pycache__
python3 relay.py --target fsm --port 1515 --amqp rabbit
