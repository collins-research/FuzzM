package jfuzz.engines.messages;

import jfuzz.engines.EngineName;

public class PauseMessage extends Message {

	QueueName target;
	public PauseMessage(EngineName source, QueueName target) {
		super(source,QueueName.PauseMessage);
		this.target = target;
	}

	@Override
	public void handleAccept(MessageHandler handler) {
		handler.handleMessage(this);
	}

	@Override
	public String toString() {
		return "Message: [Pipeline: Pause] " + target + " from " + source + ":" + sequence;
	}

}
