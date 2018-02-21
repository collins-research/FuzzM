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

/**
 * 
 * Tells target queue to resume sending messages.
 *
 */
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
