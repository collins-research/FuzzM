/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.lustre.generalize;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import fuzzm.lustre.SignalName;
import fuzzm.lustre.evaluation.Simulator;
import fuzzm.util.Debug;
import fuzzm.util.ID;
import fuzzm.value.bound.BoundValue;
import fuzzm.value.hierarchy.BooleanType;
import fuzzm.value.hierarchy.EvaluatableType;
import fuzzm.value.hierarchy.EvaluatableValue;
import fuzzm.value.hierarchy.IntegerType;
import fuzzm.value.hierarchy.RationalType;
import fuzzm.value.instance.BooleanInterval;
import fuzzm.value.instance.IntegerInfinity;
import fuzzm.value.instance.IntegerInterval;
import fuzzm.value.instance.RationalInfinity;
import fuzzm.value.instance.RationalInterval;
import jkind.lustre.NamedType;
import jkind.lustre.Type;

public class Generalizer {

	protected final Simulator simulator;
	ValueGeneralizer<BooleanType>  booleanGen  = new DiscreteIntervalGeneralizer<BooleanType>();
	ValueGeneralizer<IntegerType>  intervalGen = new DiscreteIntervalGeneralizer<IntegerType>();
	ValueGeneralizer<IntegerType>  integerGen  = new IntegerIntervalGeneralizer();
	ValueGeneralizer<RationalType> rationalGen = new RationalIntervalGeneralizer();
	private static final EvaluatableType<IntegerType> integerMaxInterval = new IntegerInterval(IntegerInfinity.NEGATIVE_INFINITY,IntegerInfinity.POSITIVE_INFINITY);
	private static final EvaluatableType<RationalType> rationalMaxInterval = new RationalInterval(RationalInfinity.NEGATIVE_INFINITY,RationalInfinity.POSITIVE_INFINITY);
	private static final EvaluatableType<BooleanType> boolMaxInterval = BooleanInterval.ARBITRARY;

	public Generalizer(Simulator simulator) {
		this.simulator = simulator;
	}
	
	private Map<SignalName,EvaluatableValue> generalize(List<SignalName> indicies) {
		Map<SignalName,EvaluatableValue> res = new HashMap<>();
		//System.out.println(ID.location());
		//System.out.println(ID.location() + "Starting Event Driven Generalization ..");
		//System.out.println(ID.location());
		for (SignalName si : indicies) {
			if (Debug.isEnabled()) System.err.println(ID.location() + "Generalizing   : " + si + " ..");
			EvaluatableValue interval = generalize(si);
			if (Debug.isEnabled()) System.err.println(ID.location() + "Generalization : " + si + " = " + interval);
			res.put(si, interval);
		}
		//System.out.println(ID.location());
		//System.out.println(ID.location() + "Generalization Complete.");
		//System.out.println(ID.location());
		return res;
	}
	
	public Map<SignalName,EvaluatableValue> eventBasedGeneralization(List<SignalName> signalNames) {
		Map<SignalName,EvaluatableValue> genMap;
		{
			long startTime = System.currentTimeMillis();
			try {
				genMap = generalize(signalNames);
			} catch (Throwable t) {
				Debug.setEnabled(true);
				try {
					System.err.println("Retry failed Simulation ..");
					genMap = generalize(signalNames);
				} catch (Throwable z) {
					System.err.flush();
					throw z;
				}
			}
			long endTime = System.currentTimeMillis();
			System.out.println(ID.location() + "Event Based Generalization Time = " + (endTime - startTime) + " ms");
		}
		return genMap;
	}
	
	// All of this case splitting could be avoided if the generalization class extended 
	// the appropriate types. Or, more to the point, if generalization were part of the
	// interface.
	public EvaluatableValue generalize(SignalName si) {
		BoundValue    bv = simulator.getBinding(si.name.name, si.time);
		EvaluatableValue curr = bv.getValue();
		Type type = bv.type;
		if (type == NamedType.INT) {
			@SuppressWarnings("unchecked")
			EvaluatableType<IntegerType> intCurr = (EvaluatableType<IntegerType>) curr;
			//System.out.println(ID.location() + "Generalizing : " + si);
			EvaluatableValue res = integerGen.generalize(simulator, si, intCurr, integerMaxInterval);
			//System.out.println(ID.location() + "Done : " + si + " = " + res);
			return res;
		} else if (type == NamedType.BOOL) {
			@SuppressWarnings("unchecked")
			EvaluatableType<BooleanType> boolCurr = (EvaluatableType<BooleanType>) curr;
			return booleanGen.generalize(simulator, si, boolCurr, boolMaxInterval);
		} else if (type == NamedType.REAL) {
			@SuppressWarnings("unchecked")
			EvaluatableType<RationalType> rationalCurr = (EvaluatableType<RationalType>) curr;
			return rationalGen.generalize(simulator, si, rationalCurr, rationalMaxInterval);
		} else {
			@SuppressWarnings("unchecked")
			EvaluatableType<IntegerType> rangeCurr = (EvaluatableType<IntegerType>) curr;
			return intervalGen.generalize(simulator, si, rangeCurr, integerMaxInterval);
		}
	}

}
