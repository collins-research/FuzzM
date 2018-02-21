/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.engines;

import fuzzm.FuzzMConfiguration;
import fuzzm.engines.messages.Message;
import fuzzm.engines.messages.MessageHandlerThread;
import fuzzm.engines.messages.TestVectorMessage;
import jkind.lustre.Program;

/**
 * We extend the Engine class once for each stage in
 * our processing pipeline.
 *
 * @param <Model>
 */
public abstract class Engine extends MessageHandlerThread implements Runnable {
	protected final Program model;
	protected final FuzzMConfiguration cfg;
	private final Director director;
	
	// Approximate queue size in bytes
	static final int QUEUE_SIZE_1M = 1000000;
	static final int QUEUE_SIZE_1K =   10000;

	// The director process will read this from another thread,
	// so we make it volatile
	protected volatile Throwable throwable;

	public Engine(EngineName name, FuzzMConfiguration cfg, Director director) {
		super(name);
		//this.name = name;
		this.model = cfg.model;
		this.cfg = cfg;
		this.director = director;
	}

	protected abstract void main();

	@Override
	public void run() {
		try {
			main();
		} catch (Throwable t) {
			throwable = t;
		}
	}

	public String getName() {
		return name.toString();
	}

	public Throwable getThrowable() {
		return throwable;
	}

	@Override
	public void broadcast(Message message) {
		director.broadcast(message);
	}

	@Override
	public void broadcast(TestVectorMessage message) {
		director.broadcast(message);
	}
}

