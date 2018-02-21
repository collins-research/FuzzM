#! /bin/bash
umask 000
chmod a+rw *.py
rm -rf __pycache__
python3 monitor.py
