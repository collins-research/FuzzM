#! /bin/bash

chmod a+rw *.py

python ./generate-tftp-lus.py > tftp.lus

java -ea -jar /usr/local/bin/fuzzm.jar -fuzzm tftp.lus --amqp rabbit 2> fuzzm.err | grep -i "pipeline"
