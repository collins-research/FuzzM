/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.engines;

import java.util.Map;

import fuzzm.FuzzMConfiguration;
import fuzzm.engines.messages.CounterExampleMessage;
import fuzzm.engines.messages.ExitException;
import fuzzm.engines.messages.FeatureID;
import fuzzm.engines.messages.GeneralizedMessage;
import fuzzm.engines.messages.QueueName;
import fuzzm.engines.messages.ReceiveQueue;
import fuzzm.engines.messages.TestVectorMessage;
import fuzzm.engines.messages.TransmitQueue;
import fuzzm.lustre.FuzzProgram;
import fuzzm.lustre.generalize.PolyGeneralizationResult;
import fuzzm.lustre.generalize.PolygonalGeneralizer;
import fuzzm.poly.RegionBounds;
import fuzzm.util.Debug;
import fuzzm.util.EvaluatableSignal;
import fuzzm.util.FuzzMInterval;
import fuzzm.util.FuzzmName;
import fuzzm.util.ID;
import fuzzm.util.IntervalVector;
import fuzzm.util.TypedName;
import jkind.lustre.Program;

/**
 * The Generalization engine takes counter examples from the
 * solver and generalizes them.
 *
 * @param <SModel>
 */
public class GeneralizationEngine extends Engine {

	final ReceiveQueue<CounterExampleMessage>  cequeue;
	final TransmitQueue<GeneralizedMessage>    genserver;
	// final TransmitQueue<IntervalVectorMessage> intserver;
	//List<VarDecl> inputNames;
//	private static final SimulationResults TRUE = new ConcreteSimulationResults();

	public GeneralizationEngine(FuzzMConfiguration cfg, Director director) {
		super(EngineName.GeneralizationEngine, cfg, director);
		cequeue = new ReceiveQueue<CounterExampleMessage>(0,this);

		genserver = new TransmitQueue<GeneralizedMessage>(this,QueueName.GeneralizedMessage);
		// intserver = new TransmitQueue<IntervalVectorMessage>(this,QueueName.IntervalVectorMessage);
		this.tx.add(genserver);
		// this.tx.add(intserver);
	}
	
	@Override
	protected void handleMessage(CounterExampleMessage m) {
		cequeue.push(m);
	}
	
	@Override
	protected void handleMessage(TestVectorMessage m) {
		assert(false);
	}	

//	@SuppressWarnings("unused")
//	private BooleanCtx packageAssertions (){
//		List<Expr> assertions = model.getMainNode().assertions;
//		BooleanCtx assertionCtx = new BooleanCtx(assertions);
//
//		assertionCtx.bind(FuzzmName.assertion);
//		Expr andedExpr = assertionCtx.getExpr();
//		
//		Expr assertExpr = new IdExpr(FuzzmName.assertion);
//		Expr preassert  = new UnaryExpr(UnaryOp.PRE, assertExpr);
//
//		Expr arrowRHS     = new BinaryExpr(preassert, BinaryOp.AND, andedExpr);
//		Expr assertionRHS = new BinaryExpr(andedExpr, BinaryOp.ARROW, arrowRHS);
//
//		assertExpr = assertionCtx.define(FuzzmName.assertion, NamedType.BOOL, assertionRHS);
//		assertionCtx.setExpr(assertExpr);
//		return assertionCtx;
//	}
	
	GeneralizedMessage generalizeCounterExample(CounterExampleMessage m) {
		// For now we just generalize.
		// TODO: we eventually want to target a vector.
		int k = m.counterExample.size();
		assert(k > 0);

		
		//System.out.println(ID.location() + m);
		Program testMain = FuzzProgram.fuzz(model,m.prop);
		//System.out.println(ID.location() + "\n" + testMain);
		
		EvaluatableSignal evaluatableCEX = m.counterExample.evaluatableSignal();
		
		// Polygonal generalization ..

		System.out.println(ID.location() + "Starting Generalization ..");
		PolyGeneralizationResult polyCEX = PolygonalGeneralizer.generalizeInterface(evaluatableCEX,m.name,FuzzmName.fuzzProperty,m.fns,testMain);
		if (Debug.isEnabled()) {
			System.out.println(ID.location() + "Generalization : " + polyCEX);
			//System.out.println(ID.location() + "ACL2 : " + polyCEX.toACL2());
		}

		// Event-based generalization ..
//		
// 		Simulator genSim = Simulator.newSimulator(evaluatableCEX,m.fns, FuzzMName.fuzzProperty, testMain, TRUE);
//		Generalizer generalizer = new Generalizer(genSim);
//		
//		List<SignalName> signalNames = m.counterExample.signalNames();
//		Collections.shuffle(signalNames);
//		Map<SignalName,EvaluatableValue> genMap = generalizer.eventBasedGeneralization(signalNames);
		
//		IntervalSignal res = new IntervalSignal();
//		for (int time=0;time<m.counterExample.size();time++) {
//			IntervalVector iv = new IntervalVector();
//			RatVect cv = m.counterExample.get(time);
//			for (TypedName name : cv.keySet()) {
//				SignalName sn = new SignalName(name,time);
//				EvaluatableValue itz = genMap.get(sn);
//				FuzzMInterval bkz = boundInterval(itz,cfg.getSpan().get(name));
//				iv.put(name, bkz);
//			}	
//			res.add(iv);
//		}
		
		/*
		FuzzMModel cex = new FuzzMModel(testMain.getMainNode(),m.counterExample); 
		SimpleModel sm = cex.toSimpleModel();
		Specification specification = new Specification(testMain.getMainNode(),testMain.functions,true,false);
		// Modifies sm ..
		try {
			ModelReconstructionEvaluator.reconstruct(specification, sm, FuzzMName.fuzzProperty, k, true);
			ModelGeneralizer mg = new ModelGeneralizer(specification,FuzzMName.fuzzProperty,sm,k);
			//List<StreamIndex> z = m.signal.encode().keySet().stream().map(x -> StreamIndex.decode(x)).collect(Collectors.toList());
			//Collections.shuffle(z);
			//List<StreamIndex> streamIndices = new ArrayList<>();
			//for (SignalName sn: signalNames) {
			//    streamIndices.add(new StreamIndex(sn.name,sn.time));
			//}
			Model gem;
			{
				long startTime = System.currentTimeMillis();
				gem = mg.generalize();
				long endTime = System.currentTimeMillis();
				System.out.println(ID.location() + "JKind Generalization Time = " + (endTime - startTime) + " ms");
			}
			res = new IntervalSignal(k, testMain.getMainNode().inputs, gem, cfg.getSpan());
			for (int time=0;time<res.size();time++) {
				IntervalVector iv = res.get(time);
				for (String name : iv.keySet()) {
					SignalName sn = new SignalName(name,time);
					//EvaluatableValue itz = genMap.get(sn);
					FuzzMInterval bkz = iv.get(name);
					//System.out.println(ID.location() + "Generalized Value " + sn + " : " + bkz); // + " ~=~ "+ itz);
					//assert(itz.getLow().equals(bkz.min));
					//assert(itz.getHigh().equals(bkz.max));
				}
			}

		} catch (Throwable t) {
			System.out.println(ID.location() + "JKind Generalization Failed : " + m);
			System.out.flush();
			throw new Error(t);
		}
		*/
		
		if(m.id.constraintID == -1){
			// here the span holds its default values		  
			initSpan(polyCEX.result.intervalBounds(), m.id);
			// now the span holds the (possibly new) actual input bounds(from vacuous constraint)
		}		
		return new GeneralizedMessage(name,m,polyCEX);
	}

//	private FuzzMInterval boundInterval(EvaluatableValue itz, FuzzMInterval FuzzMInterval) {
//		InstanceType<?> max = ((EvaluatableType<?>) itz).getHigh();
//		InstanceType<?> min = ((EvaluatableType<?>) itz).getLow();
//		BigFraction bmax = max.isFinite() ? ((RationalValue) max.rationalType()).value() : FuzzMInterval.max;
//		BigFraction bmin = min.isFinite() ? ((RationalValue) min.rationalType()).value() : FuzzMInterval.min;
//		return new FuzzMInterval(FuzzMInterval.type,bmin,bmax);
//	}

	private void initSpan (Map<TypedName,RegionBounds> zed, FeatureID cid) {
		IntervalVector newSpan = new IntervalVector(cfg.getSpan());
		for (TypedName name: zed.keySet()) {
			if (newSpan.containsKey(name)) {
				FuzzMInterval iv = newSpan.get(name);
				RegionBounds  bnd = zed.get(name);
				newSpan.put(name, bnd.updateInterval(iv));
			}
		}
		cfg.setSpan(newSpan);
		System.out.println(ID.location() + "Updated Span : " + newSpan);
	}

	@Override
	protected void main() {
		System.out.println(ID.location() + name + " is starting ..");
		try {
			while (true) {
				CounterExampleMessage cem = cequeue.pop();
				try {
                    GeneralizedMessage res = generalizeCounterExample(cem);
				    genserver.push(res);
				} catch (Throwable e) {
				    Throwable cause = e;
				    while (cause.getCause() != null) {
				        cause = cause.getCause();
				    }
				    System.err.println(ID.location() + "** Generalization Exception : " + cause.getClass().getName());
				}
			}
		} catch (ExitException e) {

		}
		System.out.println(ID.location() + name + " is exiting.");
	}

}
