# FSM  Model

A simple example of a UDP packet-driven finite state machine.

The specification for the FSM model is [here](SPEC.md)

A c++ implementation of the FSM is [here](fsm_demo/fsm.cpp)

A Lustre model, based on the FSM spec, is [here](fsm.lus).  Note that, because FuzzM is memory-less, 
we use uninterpreted functions to represent the unknown initial state of the FSM.

A relay for the FSM is [here](relay.py).

## Running The Example

Running this example is simplest using [Docker](../../INSTALLING.md).

To start the example, run the following commands from the `FuzzM/examples/fsm-model/` directory:

```bash
docker-compose up
```

To stop the example:

```bash
docker-compose down
```

## Fuzz-Off

See this [README](fsm_demo/README.md) for directions on running the Fuzz-Off
