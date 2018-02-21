#! /bin/bash

java -ea -jar /usr/local/bin/fuzzm.jar -fuzzm fsm.lus -target rabbit 2> fuzzm.err | grep -i "pipeline"

