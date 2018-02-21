package jfuzz.engines.messages;

import jfuzz.engines.EngineName;
import jfuzz.util.RatSignal;

/**
 * The Test Vector message contains a specific solution to the
 * constraint.
 * 
 * Consumed by the Output Engine.
 */
public class TestVectorMessage extends FeatureMessage {

	public RatSignal signal;

	public TestVectorMessage(EngineName source, FeatureID id, RatSignal signal, long sequence) {
		super(source,QueueName.TestVectorMessage,id,sequence);
		this.signal = signal;
	}
	
	public TestVectorMessage(EngineName source, GeneralizedMessage m, RatSignal signal) {
		this(source,m.id,signal,m.sequence);
	}
	
	@Override
	public void handleAccept(MessageHandler handler) {
		handler.handleMessage(this);
	}
	
	@Override
	public String toString() {
		return "";
		//return "Message: [Vector] " + sequence + ":" + id + " : " + signal.toString();
	}

	@Override
	public int bytes() {
		return 1 + signal.bytes();
	}
	
}
