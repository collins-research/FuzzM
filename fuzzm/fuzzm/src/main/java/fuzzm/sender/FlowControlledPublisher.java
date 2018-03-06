/* 
 * Copyright (C) 2018, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.sender;

import java.io.IOException;
import java.util.concurrent.TimeoutException;

import com.rabbitmq.client.AMQP;
import com.rabbitmq.client.AMQP.BasicProperties;
import com.rabbitmq.client.BuiltinExchangeType;
import com.rabbitmq.client.Channel;
import com.rabbitmq.client.Connection;
import com.rabbitmq.client.ConnectionFactory;
import com.rabbitmq.client.Consumer;
import com.rabbitmq.client.DefaultConsumer;
import com.rabbitmq.client.Envelope;

public class FlowControlledPublisher {

    String exchangeName;
    String target;
    
    public FlowControlledPublisher(String exchangeName, String target) throws IOException, TimeoutException {
        super();
        this.exchangeName = exchangeName;
        this.target = target;
        initConnection();
    }

    Channel pubChannel;
    Connection pubConnection;
    Channel flowCtrlChannel;
    Connection flowCtrlConnection;

    private void initConnection() throws TimeoutException, IOException {
        ConnectionFactory factory = new ConnectionFactory();
        factory.setHost(target);
        pubConnection = factory.newConnection();
        pubChannel = pubConnection.createChannel();
        pubChannel.exchangeDeclare(exchangeName, "direct");

        flowCtrlConnection = factory.newConnection();
        flowCtrlChannel = flowCtrlConnection.createChannel();
        flowCtrlChannel.exchangeDeclare(exchangeName + "_FLOW_CTRL", BuiltinExchangeType.DIRECT);
        String flowCtrlQueueName = flowCtrlChannel.queueDeclare().getQueue();
        flowCtrlChannel.queueBind(flowCtrlQueueName, exchangeName + "_FLOW_CTRL", "FLOW_CTRL");

        Consumer flowControlConsumer = new DefaultConsumer(flowCtrlChannel) {
            @Override
            public void handleDelivery(String consumerTag, Envelope envelope, AMQP.BasicProperties properties,
                    byte[] body) {
                handleFlowControlMessage(consumerTag, envelope, properties, body);
            }

        };

        flowCtrlChannel.basicConsume(flowCtrlQueueName, true, flowControlConsumer);
    }
    
    volatile long PauseCount = 0;

    public void handleFlowControlMessage(String consumerTag, Envelope envelope, AMQP.BasicProperties properties,
            byte[] body) {
        String s = new String(body);
        if (s.equals("PAUSE")) {
            PauseCount++;
        } else if (s.equals("RESUME")) {
            if (PauseCount > 0) PauseCount--;
        } else {
            throw new IllegalArgumentException();
        }
    }

    public void close() throws IOException, TimeoutException {
        pubChannel.close();
        pubConnection.close();
        flowCtrlChannel.close();
        flowCtrlConnection.close();
    }

    public void basicPublish(String exchange, String routingKey, BasicProperties props, byte[] body)
            throws TimeoutException, IOException {
        while (true) {
            try {
                while (PauseCount > 0) ;
                pubChannel.basicPublish(exchange, routingKey, props, body);
                break;
            } catch (IOException e) {
                initConnection();
            }
        }
    }

}
