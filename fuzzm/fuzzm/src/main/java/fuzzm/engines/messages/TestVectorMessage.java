/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.engines.messages;

import fuzzm.engines.EngineName;
import fuzzm.util.RatSignal;

/**
 * The Test Vector message contains a specific solution to the
 * constraint.
 * 
 * Consumed by the Output Engine.
 */
public class TestVectorMessage extends FeatureMessage {

	public RatSignal signal;

	public TestVectorMessage(EngineName source, FeatureID id, String name, RatSignal signal, long sequence) {
		super(source,QueueName.TestVectorMessage,id,name,sequence);
		this.signal = signal;
	}
	
	public TestVectorMessage(EngineName source, GeneralizedMessage m, RatSignal signal) {
		this(source,m.id,m.name,signal,m.sequence);
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
