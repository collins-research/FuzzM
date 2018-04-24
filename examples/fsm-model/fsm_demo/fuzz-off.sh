#!/bin/bash

ulimit -c 0
if [ $# -eq 0 ]
then
	echo "Must specify a fuzzer: afl | honggfuzz"
	exit
else
	if [ $1 == "afl" ]
		then
		echo core >/proc/sys/kernel/core_pattern
		pushd .
		cd /sys/devices/system/cpu
    		echo performance | tee cpu*/cpufreq/scaling_governor
		popd
		export AFL_PERSISTANT=1 
		afl-fuzz -t 4000 -m 8G -i fuzz-off/corpus -o fuzz-off/afl-crashes ./fsm-afl

	elif [ $1 == "honggfuzz" ]
		then
        mkdir fuzz-off/honggfuzz-out
		honggfuzz -f fuzz-off/corpus -V -C -S -z -P -n 1 -w fuzz-off/honggfuzz-out -- ./fsm-hongg
	else
            echo "Must specify a fuzzer: afl | honggfuzz"
	    exit
        fi
fi
