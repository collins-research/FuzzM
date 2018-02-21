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
import fuzzm.value.poly.GlobalState;

/**
 * The messages passed around the FuzzM ecosystem.  Note that each
 * message is associated with a specific constraint ID.  Each message
 * also contains a sequence identifier.  The sequence identifier 
 * evolves over time and should be uniquely generated for each
 * message.  Note, however, that new messages often inherit a
 * sequence identifier from their originating message.
 *
 */
public abstract class Message {
	final public long sequence;
	final public EngineName source;
	final public QueueName  sourceQueue;
	public Message(EngineName source, QueueName sourceQueue) {
		this.source = source;
		this.sourceQueue = sourceQueue;
		this.sequence = GlobalState.next_sequence_id();
	}
	public Message(EngineName source, QueueName sourceQueue, long sequence) {
		this.source = source;
		this.sourceQueue = sourceQueue;
		this.sequence = sequence;
	}
	public abstract void handleAccept(MessageHandler handler);
	public Message pauseRequest(EngineName newsource) {
		return new PauseMessage(newsource,this.sourceQueue);
	}
	public Message resumeRequest(EngineName newsource) {
		return new ResumeMessage(newsource,this.sourceQueue);
	}
	public int bytes() {
		return 1;
	}
}

