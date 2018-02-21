package jfuzz.engines.messages;

import jfuzz.util.ID;

public class TransmitQueue<M extends Message> extends TransmitQueueBase {

	public TransmitQueue(MessageHandlerThread parent, QueueName queue) {
		super(parent,queue);
	}

	public void push(M m) {
		do {
			if (paused()) {
				System.out.println(ID.location() + "[pause]  " + parent.name);
				synchronized (this) {
					try {					
						wait();
					} catch (InterruptedException e) {}
				}
				System.out.println(ID.location() + "[resume] " + parent.name);				
			}
		} while (paused());
		parent.broadcast(m);
	}
	
	public void pushTest(TestVectorMessage m) {
		do {
			if (paused()) {
				System.out.println(ID.location() + "[pause]  " + parent.name);			
				synchronized (this) {
					try {
						wait();
					} catch (InterruptedException e) {};
				}
				System.out.println(ID.location() + "[resume] " + parent.name);
			}
		} while (paused());
		parent.broadcast(m);
	}


}
