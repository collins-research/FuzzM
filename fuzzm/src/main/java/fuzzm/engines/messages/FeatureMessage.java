package jfuzz.engines.messages;

import jfuzz.engines.EngineName;

abstract public class FeatureMessage extends Message {
	public FeatureID id;
	public FeatureMessage(EngineName source, QueueName queue, FeatureID id, long sequence) {
		super(source,queue,sequence);
		this.id = id;
	}
	public FeatureMessage(EngineName source, QueueName queue, FeatureID id) {
		super(source,queue);
		this.id = id;
	}
}
