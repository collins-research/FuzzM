/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.engines.messages;

import java.util.ArrayList;
import java.util.Collection;

import fuzzm.engines.EngineName;

/**
 * As the Engine base class, Message Handler dictates
 * how each engine responds to and sends messages.
 *
 */
public abstract class MessageHandlerThread extends MessageHandler {
	//protected final Queue<Message> incoming = new LinkedList<>();
	public boolean exit = false;
	public final EngineName name;
	protected Collection<TransmitQueueBase> tx = new ArrayList<>();
	
	public MessageHandlerThread(EngineName name) {
		this.name = name;
	}
	
//	public void receiveMessage(Message message) {
//		message.handleAccept(this);
//	}

	public static void sleep(int millis) {
		boolean done = false;
		while (!done) {
			try {
				Thread.sleep(millis);
				done = true;
			} catch (InterruptedException e) {}
		}
	}
	
	//protected abstract boolean emptyMessageQueue();
	
	/*
	 * protected void waitForNextMessage() throws ExitException {
		while (emptyMessageQueue()) {
			sleep(10);
			processMessages();
		}
	}
	 */

	@Override
	final public void handleMessage(PauseMessage m) {
		for (TransmitQueueBase t: tx) {
			t.handleMessage(m);
		}
	}
	
	@Override
	final public void handleMessage(ResumeMessage m) {
		for (TransmitQueueBase t: tx) {
			t.handleMessage(m);
		}
	}
	
	final protected void handleMessage(ExitMessage m) {
		exit = true;
	}

	abstract public void broadcast(Message message);
	abstract public void broadcast(TestVectorMessage message);

}

