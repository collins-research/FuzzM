package jfuzz.engines;

import java.math.BigInteger;

import jfuzz.JFuzzConfiguration;
import jfuzz.engines.messages.ConstraintMessage;
import jfuzz.engines.messages.CounterExampleMessage;
import jfuzz.engines.messages.ExitException;
import jfuzz.engines.messages.QueueName;
import jfuzz.engines.messages.ReceiveQueue;
import jfuzz.engines.messages.TestVectorMessage;
import jfuzz.engines.messages.TransmitQueue;
import jfuzz.engines.messages.UnsatMessage;
//import jfuzz.legacy.evaluation.EventBasedIntervalSimulator;
//import jfuzz.legacy.evaluation.EventBasedSimulator;
//import jfuzz.legacy.optimize.IntervalOptimizer;
//import jfuzz.legacy.value.EvaluatableValue;
import jfuzz.lustre.FuzzProgram;
import jfuzz.lustre.optimize.PolygonalOptimizer;
import jfuzz.solver.Solver;
import jfuzz.solver.SolverResults;
import jfuzz.util.Debug;
import jfuzz.util.EvaluatableSignal;
import jfuzz.util.ID;
import jfuzz.util.IntervalVector;
import jfuzz.util.JFuzzName;
import jfuzz.util.RatSignal;
import jfuzz.util.RatVect;
import jfuzz.util.TypedName;
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
	JFuzzConfiguration cfg;
	
	// private static final SimulationResults TRUE = new ConcreteSimulationResults();

	public SolverEngine(JFuzzConfiguration cfg, Director director) {
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
					//Map<String,EvaluatableValue> intervalValues[] = counterExample.intervalValues();
					//EventBasedSimulator ratSim = new EventBasedIntervalSimulator(intervalValues, JFuzzName.fuzzProperty, newMain);
					//IntervalOptimizer optimizer = new IntervalOptimizer(ratSim);
					//System.out.println(ID.location() + "Initial Solution : " + k + "*" + counterExample.get(0).size());
					EvaluatableSignal evaluatableCEX = counterExample.evaluatableSignal();
					//System.out.println(ID.location() + "Simulating ..");
					//Simulator evSim = Simulator.newSimulator(evaluatableCEX, sr.fns, JFuzzName.fuzzProperty, generalizeMain, TRUE);
					//IntervalOptimizer evOpt = new IntervalOptimizer(evSim);
					RatSignal targetSignal = (cfg.asteroid) ? asteroidTarget(m.optimizationTarget, counterExample, cfg.getSpan())
							: m.optimizationTarget;
					EvaluatableSignal evaluatableTarget = targetSignal.evaluatableSignal();	
					evaluatableTarget.normalize(evaluatableCEX);
					if (Debug.isEnabled()) System.err.println(ID.location() + "Initial Solution    : " + evaluatableCEX);
					if (Debug.isEnabled()) System.err.println(ID.location() + "Optimization Target : " + evaluatableTarget + " * " + cfg.asteroid);

					//evaluatableCEX = evOpt.optimizeInterface(cfg.getSpan(), evaluatableCEX, evaluatableTarget);					
					
					//System.out.println(ID.location() + "Starting Optimization ..");
					sr = PolygonalOptimizer.optimize(sr, targetSignal, JFuzzName.fuzzProperty, generalizeMain);
					//System.out.println(ID.location() + "Optimized Solution  : " + sr.cex);
					// counterExample = evaluatableCEX.ratSignal();
					//System.out.println(ID.location() + "Optimized Solution : " + sr.cex.size() + "*" + sr.cex.get(0).size());
					cexserver.push(new CounterExampleMessage(name,m,sr));
				} else {
					satserver.push(new UnsatMessage(name,m));
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
