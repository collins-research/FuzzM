/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
 package fuzzm.engines;

import java.util.List;

import fuzzm.FuzzMConfiguration;
import fuzzm.engines.messages.ConstraintMessage;
import fuzzm.engines.messages.ExitException;
import fuzzm.engines.messages.ExitMessage;
import fuzzm.engines.messages.FeatureID;
import fuzzm.engines.messages.GeneralizedMessage;
import fuzzm.engines.messages.QueueName;
import fuzzm.engines.messages.ReceiveQueue;
import fuzzm.engines.messages.TestVectorMessage;
import fuzzm.engines.messages.TransmitQueue;
import fuzzm.engines.messages.UnsatMessage;
import fuzzm.heuristic.FeatureException;
import fuzzm.heuristic.Features;
import fuzzm.heuristic.HeuristicInterface;
import fuzzm.lustre.BooleanCtx;
import fuzzm.util.ID;
import fuzzm.util.RatSignal;
import jkind.lustre.BoolExpr;
import jkind.lustre.VarDecl;

/**
 * The Test Heuristic engine is responsible for choosing
 * the next feature to attack.
 *
 * @param <Model>
 */
public class TestHeuristicEngine extends Engine {

	final ReceiveQueue<GeneralizedMessage>      genqueue;
	final ReceiveQueue<UnsatMessage>             unqueue;
	final TransmitQueue<ConstraintMessage>    testserver;
	final TransmitQueue<ExitMessage>          exitserver;
	List<VarDecl> inputs;
	Features featureList;
	//int outstandingFeatures = 0;
	//int minOutstanding = 0;
	
	// TODO : replace this with something more elegant.
	boolean boundLock = true;
	FuzzMConfiguration cfg;
	
	public TestHeuristicEngine(FuzzMConfiguration cfg, Director director) {
		super(EngineName.TestHeuristicEngine, cfg, director);
		inputs = model.getMainNode().inputs;
		genqueue = new ReceiveQueue<GeneralizedMessage>(QUEUE_SIZE_1K,this);
		unqueue  = new ReceiveQueue<UnsatMessage>(QUEUE_SIZE_1K,this);
		
		testserver = new TransmitQueue<ConstraintMessage>(this,QueueName.ConstraintMessage);
		exitserver = new TransmitQueue<ExitMessage>(this,QueueName.ExitMessage);
		this.tx.add(testserver);
		this.tx.add(exitserver);

		featureList = cfg.extractFeatures();
		//outstandingFeatures = 0;
		//minOutstanding = Math.min(4,featureList.size());
		this.cfg = cfg;	
	}
	
	@Override
	protected void handleMessage(TestVectorMessage m) {
		// TODO: something to update our statistics (?)
		// If we ever want to process test vectors here, we
		// need to add this thread to the testVectorEngines
		// in the Director.
		assert(false);
	}

	@Override
	protected void handleMessage(GeneralizedMessage m) {
		FeatureID cid = m.id;
		int id = cid.constraintID;
		if (id == -1) {
		    // TODO: clean up span/bound processing ..
			boundLock = false;
			return;
		}
		//outstandingFeatures--;
		genqueue.push(m);
	}

	@Override
	protected void handleMessage(UnsatMessage m) {
		//outstandingFeatures--;
		unqueue.push(m);
	}


	@Override
	protected void main() {
		//
		// TODO: We have lots of work to do on the testing heuristics.
		//
		// We should probably spend our time initially establishing
		// bounds on the input values and weeding out UNSAT features.
		// 
		// It may then make sense to probe the state space randomly
		// to identify low-hanging fruit.
		// 
		// Ultimately we will want to take into consideration
		// functional relationships between variables.  This may
		// help address state space concerns.
		//
		// We probably need a more wholistic approach to constraint
		// selection, tracking property excitation and targeting 
		// those that are not meeting their distributions.
		// 
		// The random walk heuristic may want to evaluate the random
		// target points before calling the solver.  There might be
		// room for evaluating "genetic" algorithms, too.
		//
		// Along those lines, figuring out the dependencies of the 
		// "done" signal would be helpful in that department.  Perhaps
		// the genetic algorithm means generalizing one trace towards
		// another while preserving "done".
		// 
		// I suspect that some variation on generalization will be the 
		// right solution for generating nice distributions.  In the
		// mean time we need an algorithm that produces a reasonable
		// distribution using only the solver.
		//
		System.out.println(ID.location() + name + " is starting ..");
		try {
			BooleanCtx vacHyp = new BooleanCtx();
			BooleanCtx vacProp = new BooleanCtx(new BoolExpr(false));	
			RatSignal dummyTarget = new RatSignal();	
			FeatureID vacuousId = new FeatureID(-1, true);	
			ConstraintMessage cm = new ConstraintMessage(name,vacuousId,"NULL",vacHyp,vacProp,dummyTarget,dummyTarget);
			System.out.println(ID.location() + "Sending input bound constraint: " + cm);
			testserver.push(cm);
			while(boundLock){
				processQueues();
				sleep(1000);
			}
			while (true) {
				try {
					int featureID = featureList.nextFeatureID();
					HeuristicInterface Q = featureList.selectFeature(featureID);
					FeatureID id = new FeatureID(featureID,Q.objective());
					BooleanCtx hyp = Q.hyp(); // for WalkHeuristic, hyp is the bounding box (cube)
					BooleanCtx prop = Q.constraint();
					RatSignal genTarget = Q.target();
					RatSignal optTarget = RatSignal.uniformRandom(genTarget.size(),cfg.getSpan());
					Q.wait(Q.objective());
					//System.out.println(ID.location() + "Constraint Generalization Target : " + genTarget);
					//System.out.println(ID.location() + "Constraint Optimization Target   : " + optTarget);
					testserver.push(new ConstraintMessage(name,id,Q.name(),hyp,prop,optTarget,genTarget));					
				} catch (FeatureException f) {
				    if (done()) {	  			        
	                  System.out.println(ID.location() + "*** Test Heuristic is sending Exit command ..");
	                  exitserver.push(new ExitMessage(name));
	                  break;	                   
				    }
					sleep(1000);
				}
				processQueues();
			}
		} catch (ExitException e) {
		}
		System.out.println(ID.location() + name + " is exiting.");
	}

	boolean done() {
	    return featureList.done();
	}
	
	void processQueues() throws ExitException {
		if (exit) throw new ExitException();
		while (genqueue.messageReady()) {
			GeneralizedMessage m = genqueue.pop();
			if (m.id.constraintID >= 0) {
				HeuristicInterface Q = featureList.selectFeature(m.id.constraintID);
				// TODO: Improve hyp generation w/non features
				Q.sat(m.id.objective,m.time,m.counterExample,m.polyCEX);
			}
		}
		while (unqueue.messageReady()) {
			UnsatMessage m = unqueue.pop();
			if (m.id.constraintID >= 0) {
				HeuristicInterface Q = featureList.selectFeature(m.id.constraintID);
				Q.unsat(m.id.objective);
			}
		}
	}

}
