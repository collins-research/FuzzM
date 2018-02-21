/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.engines;

import java.util.ArrayList;
import java.util.List;

import fuzzm.FuzzMConfiguration;
import fuzzm.Main;
import fuzzm.engines.messages.Message;
import fuzzm.engines.messages.MessageHandlerThread;
import fuzzm.engines.messages.TestVectorMessage;
import fuzzm.util.ID;

/**
 * The Director is the top level thread, responsible
 * for accepting input, staging the other engines
 * for execution, and ultimately shutting things down.
 * 
 * @param <Model>
 */
public class Director extends MessageHandlerThread {
	// public static final MessageSource NAME = MessageSource.Director;

	private final FuzzMConfiguration settings;
	//private final long startTime;

	private final List<Engine> engines = new ArrayList<>();
	private final List<Engine> testVecEngines = new ArrayList<>();
	private final List<Thread> threads = new ArrayList<>();

	public Director(FuzzMConfiguration settings) {
		super(EngineName.DirectorEngine);
		this.settings = settings;
		//this.startTime = System.currentTimeMillis();
	}

	public void run() {
		printHeader();
		// writer.begin();
		addShutdownHook();
		createAndStartEngines();

		while (!timeout() && someThreadAlive() && !someEngineFailed()) {
			sleep(1000);
			if (exit) break;
		}

		if (removeShutdownHook()) {
			postProcessing();
			reportFailures();
		}

		for (Thread x: threads) {
			boolean done = false;
			while (! done) {
				try {
					// Wait no more than 5 seconds
					x.join(5000);
					done = true;
				} catch (InterruptedException e) {}
			}
		}

	}

	private void postProcessing() {
		// writeUnknowns();
		// writer.end();
		// writeAdvice();
		printSummary();
	}

	private final Thread shutdownHook = new Thread("shutdown-hook") {
		@Override
		public void run() {
			Director.sleep(100);
			postProcessing();
		}
	};

	private void addShutdownHook() {
		Runtime.getRuntime().addShutdownHook(shutdownHook);
	}

	private boolean removeShutdownHook() {
		try {
			Runtime.getRuntime().removeShutdownHook(shutdownHook);
			return true;
		} catch (IllegalStateException e) {
			// JVM already shutting down
			return false;
		}
	}

	private void createAndStartEngines() {
		createEngines();
		threads.forEach(Thread::start);
	}

	private void createEngines() {
		addEngine(new TestHeuristicEngine(settings,this));
		addEngine(new SolverEngine(settings,this));
		addEngine(new GeneralizationEngine(settings,this));
		if(! settings.noVectors){
			addEngine(new GeneratorEngine(settings,this));
		}
		OutputEngine ope = new OutputEngine(settings,this);
		addEngine(ope);
		testVecEngines.add(ope);
	}

	private void addEngine(Engine engine) {
		engines.add(engine);
		threads.add(new Thread(engine, engine.getName()));
	}

	

	private boolean timeout() {
		// long timeout = startTime + ((long) settings.timeout) * 1000;
		return false; // System.currentTimeMillis() > timeout
	}

	private boolean someThreadAlive() {
		return threads.stream().anyMatch(Thread::isAlive);
	}

	private boolean someEngineFailed() {
		return engines.stream().anyMatch(e -> e.getThrowable() != null);
	}

	private void reportFailures() {
		for (Engine engine : engines) {
			if (engine.getThrowable() != null) {
				System.out.println(engine.getName() + " process failed");
				engine.getThrowable().printStackTrace();
			}
		}
	}

	private void printHeader() {
		System.out.println("==========================================");
		System.out.println("  FuzzM " + Main.VERSION);
		System.out.println("==========================================");
	}

	public void broadcast(Message message) {
		String msg = message.toString();
		if (msg != "") {
			System.out.println(ID.location() + msg);
		}
		for (Engine engine : engines) {
			if (engine.name != message.source) {
				engine.handleMessage(message);
			}
		}
	}

	public void broadcast(TestVectorMessage message) {
		for (Engine engine : testVecEngines) {
			engine.handleMessage(message);
		}
	}
	
/*
	public Itinerary getValidMessageItinerary() {
		List<EngineType> destinations = new ArrayList<>();
		if (settings.reduceSupport) {
			destinations.add(EngineType.REDUCE_SUPPORT);
		}
		return new Itinerary(destinations);
	}

	public Itinerary getInvalidMessageItinerary() {
		List<EngineType> destinations = new ArrayList<>();
		if (settings.smoothCounterexamples) {
			destinations.add(EngineType.SMOOTHING);
		}
		if (settings.intervalGeneralization) {
			destinations.add(EngineType.INTERVAL_GENERALIZATION);
		}
		return new Itinerary(destinations);
	}

	private double getRuntime() {
		return (System.currentTimeMillis() - startTime) / 1000.0;
	}
*/
	private void printSummary() {
		System.out.println("    -------------------------------------");
		System.out.println("    --^^--        SUMMARY          --^^--");
		System.out.println("    -------------------------------------");
	}


}
