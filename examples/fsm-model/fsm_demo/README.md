# Running Fuzz-Off FSM Demo

From the 'FuzzM/examples/fsm-model/fsm_demo' directory:

1. Build the Docker image using `build.sh`
2. Start the Docker image using `start.sh`
3. From the container prompt, run `./fuzz-off.sh` with either `afl` or `honggfuzz` as the first parameter to start fuzzing
