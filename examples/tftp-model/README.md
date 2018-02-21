# TFTP Model

An example of a model that is intended to run against a generic TFTP
server.

A Lustre model is generated using the following python
[script](generate-tftp-lus.py).  This model employs some advanced
modeling features such as the use of uninterpreted function to
introduce non-determinism and to model large memories.

A relay for the TFTP server is [here](relay.py).  Note that this relay uses
[scapy](https://github.com/secdev/scapy) to format and send UDP packets.

## Running The Example

Running this example is simplest using [Docker](../INSTALLING.md).

To start the example, run the following commands from the `FuzzM/tftp-model` directory:

```bash
docker-compose up
```

To stop the example:

```bash
docker-compose down
```

