package jfuzz.engines.messages;

import jfuzz.engines.EngineName;

public class IntervalVectorMessage extends FeatureMessage {

    // TODO: delete this class
	public IntervalVectorMessage(EngineName source, FeatureID id) {
		super(source,QueueName.IntervalVectorMessage,id);
		// TODO: add payload
	}

	@Override
	public void handleAccept(MessageHandler handler) {
		handler.handleMessage(this);
	}
	
	@Override
	public String toString() {
		return "Message: [IntervalVector] " + sequence + ":" + id + " : "; //+ bounds.toString();
	}

}
