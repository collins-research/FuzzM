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
 * A pause request message requests that the target queue stop
 * sending messages.
 *
 */
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
