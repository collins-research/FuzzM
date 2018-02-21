/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.engines;

import java.math.BigInteger;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import fuzzm.FuzzMConfiguration;
import fuzzm.engines.messages.ExitException;
import fuzzm.engines.messages.GeneralizedMessage;
import fuzzm.engines.messages.QueueName;
import fuzzm.engines.messages.ReceiveQueue;
import fuzzm.engines.messages.TestVectorMessage;
import fuzzm.engines.messages.TransmitQueue;
import fuzzm.poly.EmptyIntervalException;
import fuzzm.poly.VariableID;
import fuzzm.util.ID;
import fuzzm.util.Rat;
import fuzzm.util.RatSignal;
import jkind.util.BigFraction;

/**
 * The Generator engine is responsible for instantiating the
 * generalized counterexamples and producing test vectors.
 * 
 * @param <Model>
 */
public class GeneratorEngine extends Engine {

	final ReceiveQueue<GeneralizedMessage>   gmqueue;
	final TransmitQueue<TestVectorMessage> testserver;
	//private boolean unbiased;
	
	public GeneratorEngine(FuzzMConfiguration settings, Director director) {
		super(EngineName.GeneratorEngine, settings, director);
		gmqueue = new ReceiveQueue<GeneralizedMessage>(QUEUE_SIZE_1K,this);

		testserver = new TransmitQueue<TestVectorMessage>(this,QueueName.TestVectorMessage);
		this.tx.add(testserver);
		
		//unbiased = settings.unbiased;
	}

	@Override
	protected void handleMessage(GeneralizedMessage m) {
		gmqueue.push(m);
	}

	RatSignal generateSignal(GeneralizedMessage gm, Map<VariableID,BigFraction> ctx) {
		return gm.nextBiasedVector(Rat.oracle.nextBoolean(),min,max,cfg.getSpan(),ctx);
	}
	
	private static final BigInteger TWO = BigInteger.valueOf(2);
	private BigInteger step = BigInteger.valueOf(100);
	private BigFraction min = new BigFraction(BigInteger.valueOf(-100));
	private BigFraction max = new BigFraction(BigInteger.valueOf( 100));
	private BigInteger count = BigInteger.valueOf(100);
	void generateTestVectors() throws ExitException {
		while (true) {
			GeneralizedMessage gm = gmqueue.pop();
			if (gm.id.constraintID != -1) {
				// TODO: We probably want to re-architect this a bit
				long startTime = System.currentTimeMillis();
				long totalSize = 0;
				int  size = gm.polyCEX.result.bytes();
				Collection<VariableID> unbound = gm.polyCEX.result.unboundVariables(); // gm.generalizedCEX
				for (@SuppressWarnings("unused") long n: gm) {
					Map<VariableID,BigFraction> ctx = new HashMap<>();
					for (VariableID vid: unbound) {
						ctx.put(vid, Rat.biasedRandom(vid.name.name.type,false,0,min,max));
					}
					try {
						RatSignal sig= generateSignal(gm,ctx); 
						TestVectorMessage m = new TestVectorMessage(name,gm,sig);
						totalSize += size;
						testserver.pushTest(m);
						if (cfg.throttle) sleep(100);
					} catch (EmptyIntervalException e) {
						System.out.println(ID.location() + "Vector Generation Failure.");
						System.exit(1);
					}
				}
				long endTime = System.currentTimeMillis();
				long delta = (endTime - startTime);
				if (delta > 10) System.out.println(ID.location() + "Vector Generation Rate = " + (1000*totalSize)/delta + " fields/s");
				count = count.subtract(BigInteger.ONE);
				if (count.signum() <= 0) {
					step = step.multiply(TWO);
					count = step;
					max = new BigFraction(step);
					min = new BigFraction(step.negate());
				}
			}
		}
	}
	
	@Override
	protected void main() {
		System.out.println(ID.location() + name + " is starting ..");		
		try {
			generateTestVectors();
		} catch (ExitException e) {
			
		}
		System.out.println(ID.location() + name + " is exiting.");		
	}
	
}
