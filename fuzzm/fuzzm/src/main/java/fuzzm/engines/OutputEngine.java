/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.engines;

import java.io.IOException;
import java.time.Duration;
import java.time.Instant;
import java.util.concurrent.TimeoutException;

import fuzzm.FuzzMConfiguration;
import fuzzm.engines.messages.CounterExampleMessage;
import fuzzm.engines.messages.ExitException;
import fuzzm.engines.messages.ReceiveQueue;
import fuzzm.engines.messages.TestVectorMessage;
import fuzzm.sender.FlowControlledPublisher;
import fuzzm.sender.OutputMsgTypes;
import fuzzm.sender.PrintSender;
import fuzzm.util.Debug;
import fuzzm.util.ID;
import fuzzm.util.RatSignal;
import fuzzm.util.RatVect;
import fuzzm.util.TypedName;
import jkind.lustre.NamedType;

/**
 * The OutputEngine sits at the end of the processing pipeline and transmits
 * test vectors. If a target is specified, it will send the vectors via UDP. If
 * debug is specified, it dumps them to stdout.
 * 
 * @param <Model>
 */
public class OutputEngine extends Engine {

    static final public int TARGET_TIMEOUT_MS = 1;
    static final public Duration CONFIG_SPEC_TRANSMIT_PERIOD = Duration.ofSeconds(5);
    Instant lastConfigSpecSentInstant;
    final PrintSender printSender;
    final ReceiveQueue<TestVectorMessage> tvqueue;
    final ReceiveQueue<CounterExampleMessage> cexqueue;
    int sequenceID;
    FlowControlledPublisher publisher;

    private static final String EXCHANGE_NAME = "fuzzm-output-engine";
    String configSpecMsg;

    public OutputEngine(FuzzMConfiguration cfg, Director director) {
        super(EngineName.OutputEngine, cfg, director);
        tvqueue = new ReceiveQueue<TestVectorMessage>(QUEUE_SIZE_1M, this);
        cexqueue = new ReceiveQueue<CounterExampleMessage>(0, this);
        if (Debug.isEnabled()) {
            printSender = new PrintSender();
        } else {
            printSender = null;
        }
        sequenceID = 0;
        lastConfigSpecSentInstant = Instant.now();

        configSpecMsg = "";
        for (TypedName key : cfg.getSpan().keySet()) {
            configSpecMsg = configSpecMsg.concat(" ");
            configSpecMsg = configSpecMsg.concat(ID.decodeString(key.name));
            configSpecMsg = configSpecMsg.concat(" ");
            assert (cfg.getSpan().get(key).type instanceof NamedType);
            configSpecMsg = configSpecMsg.concat(cfg.getSpan().get(key).type.toString());
        }

        if (cfg.target != null) {
            try {
                publisher = new FlowControlledPublisher(EXCHANGE_NAME, cfg.target);

            } catch (Exception e) {
                e.printStackTrace();
                System.exit(1);
            }

        }
    }

    @Override
    protected void handleMessage(TestVectorMessage m) {
        if (m == null) {
            throw new IllegalArgumentException();
        }
        tvqueue.push(m);
    }

    @Override
    protected void handleMessage(CounterExampleMessage m) {
        if (m == null) {
            throw new IllegalArgumentException();
        }
        cexqueue.push(m);
    }

    private void processSocketTX() throws ExitException {
        TestVectorMessage tv = tvqueue.pop_non_blocking();
        if (tv != null) {
            if (cfg.target != null) {
                send(tv.signal, OutputMsgTypes.TEST_VECTOR_MSG_TYPE.toString());
            }
            if (printSender != null) {
                printSender.send(tv);
            }
        }

        CounterExampleMessage cex = cexqueue.pop_non_blocking();
        if (cex != null) {
            if (cfg.target != null) {
                send(cex.counterExample, OutputMsgTypes.COUNTER_EXAMPLE_MSG_TYPE.toString());
            }
            if (printSender != null) {
                printSender.send(cex);
            }
        }
    }

    public void send(RatSignal values, String routingKey) {
        int time = 0;
        for (RatVect rv : values) {
            String value = "" + sequenceID + " " + time;
            for (TypedName key : cfg.getSpan().keySet()) {
                value = value.concat(" ");
                assert (rv.containsKey(key));
                value = value.concat(rv.get(key).getNumerator().toString());
                if (key.type == NamedType.REAL) {
                    value = value.concat(" ");
                    value = value.concat(rv.get(key).getDenominator().toString());
                }
            }
            // System.out.println(ID.location() + "UDP Sending Vector : " + txID);
            try {
                publisher.basicPublish(EXCHANGE_NAME, routingKey, null, value.getBytes("UTF-8"));
            } catch (IOException e) {
                e.printStackTrace();
            } catch (TimeoutException e) {
                e.printStackTrace();
            }
            sequenceID++;
            time++;
        }
    }

    public void sendConfigSpec() {
        if (cfg.target != null) {
            try {
                publisher.basicPublish(EXCHANGE_NAME, OutputMsgTypes.CONFIG_SPEC_MSG_TYPE.toString(), null,
                        configSpecMsg.getBytes("UTF-8"));
            } catch (IOException e) {
                e.printStackTrace();
            } catch (TimeoutException e) {
                e.printStackTrace();
            }
        }
    }

    @Override
    protected void main() {
        System.out.println(ID.location() + name + " is starting ..");
        sendConfigSpec();
        try {
            while (true) {
                processSocketTX();
                if (Instant.now().isAfter(lastConfigSpecSentInstant.plus(CONFIG_SPEC_TRANSMIT_PERIOD))) {
                    sendConfigSpec();
                    lastConfigSpecSentInstant = Instant.now();
                }
            }
        } catch (ExitException e) {

        }
        if (cfg.target != null) {
            try {
                publisher.close();
            } catch (IOException | TimeoutException e) {
                e.printStackTrace();
            }
        }
        System.out.println(ID.location() + name + " is exiting.");
    }
}
