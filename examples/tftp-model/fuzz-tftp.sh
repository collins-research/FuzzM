#! /bin/bash

python ./generate-tftp-lus.py > tftp.lus

java -ea -jar /usr/local/bin/fuzzm.jar -fuzzm tftp.lus --target rabbit

