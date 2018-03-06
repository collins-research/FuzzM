/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.engines.messages;
import java.util.LinkedList;
import java.util.Queue;

import fuzzm.util.ID;

/**
 * A queue for incoming messages.
 */
public class ReceiveQueue<M extends Message> {
	
	final Queue<M> queue;
	public int volume;
	private boolean paused;
	final int volumeTrigger;
	final MessageHandlerThread parent;

	public ReceiveQueue(int volumeTrigger, MessageHandlerThread parent) {
		this.volumeTrigger = volumeTrigger;
		this.parent = parent;
		this.volume = 0;
		this.paused = false;
		this.queue = new LinkedList<>();
	}
	
	// Messages coming in from other producers ..
	// called by Director via handleMessage().
	public void push(M message) {
		boolean pause = false;
		synchronized (queue) {
			queue.add(message);
			volume += message.bytes();
			if (volumeTrigger > 0 && volume >= volumeTrigger && !paused) {
				paused = true;
				pause = true;
			} else if (paused) {
				System.out.println(ID.location() + message.source + " piling on the " + message.sourceQueue +  " of " + parent.name);
			}
		}
		if (pause) parent.broadcast(message.pauseRequest(parent.name));
		synchronized (this) {
			notifyAll();
		}
	}
	
	// Consumer non-polling check ..
	public boolean messageReady() {
		return ! queue.isEmpty();
	}

	// Get a message for the consumer ..
	public M pop() throws ExitException {	
		boolean resume = false;
		M res = null;
		if (parent.exit) throw new ExitException();
		do {
			if (queue.isEmpty()) {
				
				//System.out.println(ID.location() + "[wait] " + parent.name);							
				synchronized (this) {
					try {
						wait(1000);
					} catch (InterruptedException e) {}
				}
				//System.out.println(ID.location() + "[wake] " + parent.name);	
				if (parent.exit) throw new ExitException();
			}
		} while (queue.isEmpty());
		synchronized (queue) {
			res = queue.poll();
			if (res == null) {
				throw new IllegalArgumentException();
			}
			volume -= res.bytes();
			if (volumeTrigger > 0 && (2*volume) < volumeTrigger && paused) {
				paused = false;
				resume = true;
			}
		}
		if (resume) parent.broadcast(res.resumeRequest(parent.name));
		return res;
	}

    // Get a message for the consumer ..
    public M pop_non_blocking() throws ExitException {
        boolean resume = false;
        M res = null;
        if (parent.exit)
            throw new ExitException();
        synchronized (queue) {
            res = queue.poll();
            if (res != null) {
                volume -= res.bytes();
                if (volumeTrigger > 0 && (2 * volume) < volumeTrigger && paused) {
                    paused = false;
                    resume = true;
                }
            }
        }
        if (resume)
            parent.broadcast(res.resumeRequest(parent.name));
        return res;
    }

}
