#! /bin/bash
umask 000
rm -rf fuzzm.err
rm -rf fuzzm_fsm_*
java -ea -jar /usr/local/bin/fuzzm.jar -fuzzm fsm.lus -target rabbit 2> fuzzm.err > /dev/null

