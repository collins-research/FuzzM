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
 * A queue for outgoing messages.
 */
public class TransmitQueue<M extends Message> extends TransmitQueueBase {

	public TransmitQueue(MessageHandlerThread parent, QueueName queue) {
		super(parent,queue);
	}

	public void push(M m) {
		do {
			if (paused()) {
				//System.out.println(ID.location() + "[pause]  " + parent.name);
				synchronized (this) {
					try {					
						wait(1000);
					} catch (InterruptedException e) {}
				}
				//System.out.println(ID.location() + "[resume] " + parent.name);				
			}
		} while (paused());
		parent.broadcast(m);
	}
	
	public void pushTest(TestVectorMessage m) {
		do {
			if (paused()) {
				//System.out.println(ID.location() + "[pause]  " + parent.name);			
				synchronized (this) {
					try {
						wait(1000);
					} catch (InterruptedException e) {};
				}
				//System.out.println(ID.location() + "[resume] " + parent.name);
			}
		} while (paused());
		parent.broadcast(m);
	}


}
