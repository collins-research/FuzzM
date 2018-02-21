/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.lustre.optimize;

import java.util.Collections;
import java.util.List;

import fuzzm.lustre.SignalName;
import fuzzm.lustre.evaluation.ConcreteSimulationResults;
import fuzzm.lustre.evaluation.SimulationResults;
import fuzzm.lustre.evaluation.Simulator;
import fuzzm.lustre.generalize.Generalizer;
import fuzzm.util.Debug;
import fuzzm.util.EvaluatableSignal;
import fuzzm.util.ID;
import fuzzm.util.IntervalVector;
import fuzzm.util.TypedName;
import fuzzm.value.hierarchy.EvaluatableType;
import fuzzm.value.hierarchy.EvaluatableValue;
import fuzzm.value.hierarchy.EvaluatableValueHierarchy;

public class IntervalOptimizer extends Generalizer {
	
	private static final SimulationResults TRUE = new ConcreteSimulationResults();

	public IntervalOptimizer(Simulator simulator) {
		super(simulator);
	}

	/*static UnboundFraction round(UnboundFraction x) {
		BigInteger N = x.getNumerator();
		int s = N.signum();
		N = N.abs();
		BigInteger D = x.getDenominator();
		BigInteger QR[] = N.divideAndRemainder(D);
		BigInteger Q = QR[0];
		BigInteger R = QR[1];
		if (R.shiftLeft(1).compareTo(D) >= 0) {
			Q = Q.add(BigInteger.ONE);
		}
		return new UnboundFraction((s < 0) ? Q.negate() : Q);
	}
	
	static ValueInterval round(ValueInterval x) {
		UnboundFraction min = round(x.getLow());
		UnboundFraction max = round(x.getHigh());
		return new ValueInterval(min,max);
	}*/
	
	public EvaluatableSignal optimizeInterface(IntervalVector span, EvaluatableSignal originalSignal, EvaluatableSignal targetSignal) {
		EvaluatableSignal evaluatableCEX;
		try {
			evaluatableCEX = optimize(span,originalSignal,targetSignal);
		} catch (Throwable t) {
			Debug.setEnabled(true);
			try {
				System.err.println(ID.location() + "Retry Failed Simulation ..");
				evaluatableCEX = optimize(span,originalSignal,targetSignal);
			} catch (Throwable z) {
				System.err.println(ID.location() + "Re-Caught Exception");
				System.err.flush();
				throw z;
			}
		}
		return evaluatableCEX;
	}
	
	private EvaluatableSignal optimize(IntervalVector span, EvaluatableSignal originalSignal, EvaluatableSignal targetSignal) {
		//
		// For now I have removed the vector optimization.
		//
		int k = originalSignal.size();		
		List<SignalName> allSignals = span.elaborate(k);
		Collections.shuffle(allSignals);
		EvaluatableSignal result = new EvaluatableSignal(originalSignal);
		for (int i=0;i<2;i++) {
			for (SignalName sn: allSignals) {
				int time = sn.time;
				TypedName name = sn.name;
				EvaluatableValue targetValue = targetSignal.get(time).get(name);
				//if (Debug.isEnabled()) System.err.println(ID.location() + "Optimizing " + name);
				EvaluatableValue resultValue = result.get(time).get(name);
				if (! targetValue.equals(resultValue)) {
					try {
						resultValue = optimize(sn,targetValue);
					} catch (Throwable t) {
						Debug.setEnabled(true);
						try {
							System.err.println(ID.location() + "Retry Failed Simulation ..");						
							resultValue = optimize(sn,targetValue);
						} catch (Throwable z) {
							System.err.flush();
							throw z;
						}
					}
					//System.out.println(ID.location() + "Done.");
					result.get(time).put(name,resultValue);
				}
			}
		}
		return result;
	}
	
	private EvaluatableValue optimize(SignalName sn, EvaluatableValue targetValue) {
		//System.err.println(ID.location() + sn.name + " target " + targetValue) ;
		//System.err.println(ID.location() + sn.name + " is currently " + simulator.getBinding(sn.name, sn.time).getValue()) ;
		EvaluatableValue interval = generalize(sn);
		//System.err.println(ID.location() + sn.name + " must lie in this interval : " + interval);
		EvaluatableValue resultValue;
		EvaluatableValue ratTarget   = ((EvaluatableType<?>) targetValue).rationalType();
		EvaluatableValue ratInterval = ((EvaluatableType<?>) interval).rationalType();
		if (((EvaluatableValueHierarchy) ratTarget.minus(((EvaluatableValueHierarchy) ratInterval).getLow())).signum() < 0) {
			resultValue = ((EvaluatableValueHierarchy)interval).getLow();
		} else if (((EvaluatableValueHierarchy)((EvaluatableValueHierarchy)ratInterval).getHigh().minus(ratTarget)).signum() < 0) {
			resultValue = ((EvaluatableValueHierarchy)interval).getHigh();
		} else {
		    resultValue = targetValue;
		}
		//System.out.println(ID.location() + "We choose you : " + resultValue);
		if (! simulator.isConsistent(sn,resultValue,TRUE).isSatisfactory()) assert(false);
		return resultValue;
	}
	
}
