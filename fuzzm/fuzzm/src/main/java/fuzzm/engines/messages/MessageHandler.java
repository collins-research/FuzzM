/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.engines.messages;

/* Base class for message handlers
 */
public abstract class MessageHandler {
	
	public void handleMessage(Message message) {
		message.handleAccept(this);
	}

	protected void handleMessage(CounterExampleMessage m) {
	}
	
	protected void handleMessage(GeneralizedMessage m) {
	}

	protected void handleMessage(TestVectorMessage m) {
	}

	protected void handleMessage(ConstraintMessage m) {
	}
	
	protected void handleMessage(UnsatMessage m) {
	}
	
//	protected void handleMessage(IntervalVectorMessage m) {}
	
	protected void handleMessage(PauseMessage m) {
	}
	
	protected void handleMessage(ResumeMessage m) {
	}
	
	abstract protected void handleMessage(ExitMessage m);
	
}
