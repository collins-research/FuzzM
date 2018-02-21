/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.engines.messages;

/**
 * The base class for outgoing message queues.
 */
public class TransmitQueueBase {

	final protected MessageHandlerThread parent;
	private int pauseRequests = 0;
	final QueueName queue;
	
	public TransmitQueueBase(MessageHandlerThread parent, QueueName queue) {
		this.parent = parent;
		this.queue = queue;
	}
	
	public boolean paused() {
		return (pauseRequests > 0);
	}
	
	public synchronized void handleMessage(ResumeMessage m) {
		//System.out.println(ID.location() + "Processing Resume Request  " + m.toString() + " at " + this.queue + " in " + parent.name);

		if (m.target == this.queue) {

			if (pauseRequests > 0) pauseRequests--;
			//System.out.println(ID.location() + "Acknowledging Pipeline Resume : " + m.toString());
		}
		if (pauseRequests <= 0) notifyAll();

	}

	public synchronized void handleMessage(PauseMessage m) {
		//System.out.println(ID.location() + "Processing Pause Request  " + m.toString() + " at " + this.queue + " in " + parent.name);
		if (m.target == this.queue) {
			//System.out.println(ID.location() + "Acknowledging Pipeline Pause : " + m.toString());
			pauseRequests++;
		}
	}
	
}
