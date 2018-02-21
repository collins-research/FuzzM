package jfuzz.engines.messages;

import jfuzz.engines.EngineName;

public class ResumeMessage extends Message {

	QueueName target;
	public ResumeMessage(EngineName source, QueueName target) {
		super(source,QueueName.ResumeMessage);
		this.target = target;
	}

	@Override
	public void handleAccept(MessageHandler handler) {
		handler.handleMessage(this);
	}

	@Override
	public String toString() {
		return "Message: [Pipeline: Resume] " + target + " from " + source + ":" + sequence;
	}

}
