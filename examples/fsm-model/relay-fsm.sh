#! /bin/bash
umask 000
chmod a+rw *.py
chmod a+rw /root/base-receiver/*.py
rm -rf __pycache__
rm -rf /root/base-receiver/__pycache__
python3 relay.py -ti fsm -tp 1515 -f rabbit
