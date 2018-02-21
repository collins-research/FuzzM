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

import fuzzm.FuzzMConfiguration;
import fuzzm.engines.messages.ConstraintMessage;
import fuzzm.engines.messages.CounterExampleMessage;
import fuzzm.engines.messages.ExitException;
import fuzzm.engines.messages.QueueName;
import fuzzm.engines.messages.ReceiveQueue;
import fuzzm.engines.messages.TestVectorMessage;
import fuzzm.engines.messages.TransmitQueue;
import fuzzm.engines.messages.UnsatMessage;
import fuzzm.lustre.FuzzProgram;
import fuzzm.lustre.optimize.PolygonalOptimizer;
import fuzzm.solver.Solver;
import fuzzm.solver.SolverResults;
import fuzzm.util.Debug;
import fuzzm.util.EvaluatableSignal;
import fuzzm.util.FuzzmName;
import fuzzm.util.ID;
import fuzzm.util.IntervalVector;
import fuzzm.util.RatSignal;
import fuzzm.util.RatVect;
import fuzzm.util.TypedName;
import jkind.lustre.Program;
import jkind.util.BigFraction;

/**
 * The Solver Engine is responsible for invoking the solver
 * (currently JKind) and obtaining a counterexample.
 *
 */
public class SolverEngine extends Engine {

	final ReceiveQueue<ConstraintMessage> cqueue;
	final TransmitQueue<CounterExampleMessage> cexserver;
	final TransmitQueue<UnsatMessage> satserver;
	Solver slvr;
	FuzzMConfiguration cfg;
	
	// private static final SimulationResults TRUE = new ConcreteSimulationResults();

	public SolverEngine(FuzzMConfiguration cfg, Director director) {
		super(EngineName.SolverEngine, cfg, director);

		// We limit ourselves to 4 active constraints ..
		cqueue = new ReceiveQueue<ConstraintMessage>(4,this);

		cexserver = new TransmitQueue<CounterExampleMessage>(this,QueueName.CounterExampleMessage);
		satserver = new TransmitQueue<UnsatMessage>(this,QueueName.UnsatMessage);
		this.tx.add(cexserver);
		this.tx.add(satserver);

		slvr = cfg.configureSolver();
		this.cfg = cfg;
	}
	
	@Override
	protected void handleMessage(ConstraintMessage m) {
		cqueue.push(m);
	}
	
	@Override
	protected void handleMessage(TestVectorMessage m) {
		assert(false);
	}


	@Override
	protected void main() {
		System.out.println(ID.location() + name + " is starting ..");
		try {
			//int count = 0;
			while (true) {
				//waitForNextMessage();
				ConstraintMessage m = cqueue.pop();

				try {
				    // Make things stop early ..
				    //while (count > 1) {sleep(10000);}
				    //count++;

				    slvr.randomSolver();

				    //System.out.println(ID.location() + m);
				    Program solverMain = FuzzProgram.fuzz(model,m.hyp.implies(m.prop));
				    Program generalizeMain = FuzzProgram.fuzz(model,m.prop);
				    //System.out.println(ID.location() + "\n" + newMain);			

				    SolverResults sr = slvr.invoke(solverMain);
				    RatSignal counterExample = sr.cex;
				    int k = counterExample.size();
				    if (k > 0) {
				        // System.err.println(ID.location() + "Solver Solution : " + sr);
				        //Map<String,EvaluatableValue> intervalValues[] = counterExample.intervalValues();
				        //EventBasedSimulator ratSim = new EventBasedIntervalSimulator(intervalValues, FuzzMName.fuzzProperty, newMain);
				        //IntervalOptimizer optimizer = new IntervalOptimizer(ratSim);
				        //System.out.println(ID.location() + "Initial Solution : " + k + "*" + counterExample.get(0).size());
				        EvaluatableSignal evaluatableCEX = counterExample.evaluatableSignal();
				        //System.out.println(ID.location() + "Simulating ..");
				        //Simulator evSim = Simulator.newSimulator(evaluatableCEX, sr.fns, FuzzMName.fuzzProperty, generalizeMain, TRUE);
				        //IntervalOptimizer evOpt = new IntervalOptimizer(evSim);
				        RatSignal targetSignal = m.optimizationTarget;
				        EvaluatableSignal evaluatableTarget = targetSignal.evaluatableSignal();	
				        evaluatableTarget.normalize(evaluatableCEX);
				        if (Debug.isEnabled()) System.err.println(ID.location() + "Initial Solution    : " + evaluatableCEX);
				        if (Debug.isEnabled()) System.err.println(ID.location() + "Optimization Target : " + evaluatableTarget);

				        //evaluatableCEX = evOpt.optimizeInterface(cfg.getSpan(), evaluatableCEX, evaluatableTarget);					

				        //System.out.println(ID.location() + "Starting Optimization ..");

				        sr = PolygonalOptimizer.optimize(sr, targetSignal, m.name, FuzzmName.fuzzProperty, generalizeMain);

				        if (Debug.isEnabled()) System.out.println(ID.location() + "Optimized Solution  : " + sr.cex);
				        // counterExample = evaluatableCEX.ratSignal();
				        //System.out.println(ID.location() + "Optimized Solution : " + sr.cex.size() + "*" + sr.cex.get(0).size());
				        cexserver.push(new CounterExampleMessage(name,m,sr));
				    } else {
				        satserver.push(new UnsatMessage(name,m,sr.time));
				    }
				} catch (Throwable e) {
				    e.printStackTrace(System.err);
                    Throwable cause = e;
                    while (cause.getCause() != null) {
                        cause = cause.getCause();
                    }
                    System.err.println(ID.location() + "** Solver Exception : " + cause.getClass().getName());				    
				}
			} 
		} catch (ExitException e) {
		}
		System.out.println(ID.location() + name + " is exiting.");
	}

	private static BigFraction abs (BigFraction a){
		return (a.signum() < 0) ? a.negate() : a;
	}
	
	protected static RatSignal asteroidTarget (RatSignal target, RatSignal sln, IntervalVector span){
		RatSignal res = new RatSignal();
		
		for(int time = 0; time < target.size(); time++){
			RatVect tv = target.get(time);
			RatVect sv = sln.get(time);
			for(TypedName key : tv.keySet()){
				BigFraction targetVal = tv.get(key);
				BigFraction slnVal = sv.get(key);
				BigFraction distTargetToSln = abs (targetVal.subtract(slnVal));		
				BigFraction range = span.get(key).getRange();
				
				if(distTargetToSln.compareTo(range.divide(BigInteger.valueOf(2))) < 0){
					res.put(time, key, targetVal);
				}			
				else if(slnVal.compareTo(targetVal) < 0){
					res.put(time, key, targetVal.subtract(range));	
				}
				else {
					res.put(time, key, targetVal.add(range));
				}
			} // end for key
		} // end for time
		return res;
	}
	
}
