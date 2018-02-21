package jfuzz.engines;

import java.io.IOException;
import java.time.Duration;
import java.time.Instant;
import java.util.concurrent.TimeoutException;

import com.rabbitmq.client.Channel;
import com.rabbitmq.client.Connection;
import com.rabbitmq.client.ConnectionFactory;

import jfuzz.JFuzzConfiguration;
import jfuzz.engines.messages.CounterExampleMessage;
import jfuzz.engines.messages.ExitException;
import jfuzz.engines.messages.ReceiveQueue;
import jfuzz.engines.messages.TestVectorMessage;
import jfuzz.sender.OutputMsgTypes;
import jfuzz.sender.PrintSender;
import jfuzz.util.Debug;
import jfuzz.util.ID;
import jfuzz.util.RatSignal;
import jfuzz.util.RatVect;
import jfuzz.util.TypedName;
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
    Channel channel;
    Connection connection;
    private static final String EXCHANGE_NAME = "jfuzz-output-engine";
    String configSpecMsg;

    public OutputEngine(JFuzzConfiguration cfg, Director director) {
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
                ConnectionFactory factory = new ConnectionFactory();
                factory.setHost(cfg.target);
                connection = factory.newConnection();
                channel = connection.createChannel();
                channel.exchangeDeclare(EXCHANGE_NAME, "direct");
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
                channel.basicPublish(EXCHANGE_NAME, routingKey, null, value.getBytes("UTF-8"));
            } catch (IOException e) {
                e.printStackTrace();
            }
            sequenceID++;
            time++;
        }
    }

    public void sendConfigSpec() {
        if (cfg.target != null) {
            try {
                channel.basicPublish(EXCHANGE_NAME, OutputMsgTypes.CONFIG_SPEC_MSG_TYPE.toString(), null, configSpecMsg.getBytes("UTF-8"));
            } catch (IOException e) {
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
                channel.close();
                connection.close();
            } catch (IOException | TimeoutException e) {
                e.printStackTrace();
            }
        }
        System.out.println(ID.location() + name + " is exiting.");
    }
}
