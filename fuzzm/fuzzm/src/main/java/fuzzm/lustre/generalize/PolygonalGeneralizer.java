/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.lustre.generalize;

import java.util.Collections;
import java.util.List;

import fuzzm.lustre.SignalName;
import fuzzm.lustre.evaluation.FunctionLookupEV;
import fuzzm.lustre.evaluation.PolyFunctionMap;
import fuzzm.poly.PolyBase;
import fuzzm.poly.PolyBool;
import fuzzm.poly.VariableID;
import fuzzm.util.Debug;
import fuzzm.util.EvaluatableSignal;
import fuzzm.util.ID;
import fuzzm.util.IDString;
import fuzzm.value.hierarchy.BooleanType;
import fuzzm.value.hierarchy.EvaluatableValue;
import fuzzm.value.hierarchy.IntegerType;
import fuzzm.value.hierarchy.RationalType;
import fuzzm.value.poly.BooleanPoly;
import fuzzm.value.poly.GlobalState;
import fuzzm.value.poly.IntegerPoly;
import fuzzm.value.poly.RationalPoly;
import jkind.lustre.Program;
import jkind.util.BigFraction;

public class PolygonalGeneralizer {

	protected final DepthFirstPolyGeneralizer simulator;

	public PolygonalGeneralizer(FunctionLookupEV fev, Program program) {
		this.simulator = new DepthFirstPolyGeneralizer(fev, program);
	}
	
	private PolyBool generalize(EvaluatableSignal cex, String name, IDString property) {
		//System.out.println(ID.location() + "Counterexample Depth : " + cex.size());
		EvaluatableSignal state = new EvaluatableSignal();
		List<SignalName> signals = cex.getSignalNames();
		Collections.shuffle(signals);
		for (SignalName sn: signals) {
			//System.out.println(ID.location() + "Counterexample Depth : " + state.size());
			EvaluatableValue value = cex.get(sn.name,sn.time);
			if (value instanceof BooleanType) {
				BigFraction vx = ((BooleanType) value).getValue();
				VariableID vid = VariableID.principleAlloc(sn,vx);
				state.set(sn.name,sn.time,new BooleanPoly(vid));
			} else if (value instanceof IntegerType) {
				BigFraction vx = ((IntegerType) value).getValue();
				VariableID vid = VariableID.principleAlloc(sn,vx);
				state.set(sn.name,sn.time,new IntegerPoly(new PolyBase(vid)));
			} else if (value instanceof RationalType) {
				BigFraction vx = ((RationalType) value).getValue();
				VariableID vid = VariableID.principleAlloc(sn,vx);
				state.set(sn.name,sn.time,new RationalPoly(new PolyBase(vid)));
			} else {
				throw new IllegalArgumentException();
			}
		}
		PolyBool polyRes = simulator.simulateProperty(state, name, property);
		if (! (polyRes.cex && !polyRes.isNegated())) {
		    System.err.println(ID.location() + polyRes.toString());
		    assert(false);
		}
		polyRes = polyRes.normalize();
		if (Debug.isEnabled()) { 
		    System.out.println(ID.location() + "Cex : " + cex);
		    System.out.println(ID.location() + "Generalization Result : " + polyRes);
		}
		return polyRes;
	}
	
	public static PolyGeneralizationResult generalizeInterface(EvaluatableSignal cex, String name, IDString property, FunctionLookupEV fns, Program testMain) {
		PolyGeneralizationResult res;
		synchronized (GlobalState.class) {
			long startTime = System.currentTimeMillis();
			try {
				PolygonalGeneralizer pgen2 = new PolygonalGeneralizer(fns,testMain);			
				PolyBool g2 = pgen2.generalize(cex,name,property);
				assert(g2.cex && !g2.isNegated());
				PolyFunctionMap fmap = pgen2.simulator.fmap;
				res = new PolyGeneralizationResult(g2,fmap,GlobalState.getReMap());
			} catch (Throwable t) {
				System.err.println(ID.location() + "Retrying failed PolyGeneralization ..");
				t.printStackTrace();
				Debug.setEnabled(true);
				Debug.setProof(true);
				try {
				    System.err.println(ID.location() + "Property    : " + name);
                    System.err.println(ID.location() + "Initial CEX : " + cex);
				    System.err.println(ID.location() + "Initial FNS : " + fns);
                    PolygonalGeneralizer pgen2 = new PolygonalGeneralizer(fns,testMain);			
					PolyBool g2 = pgen2.generalize(cex,name,property);
					PolyFunctionMap fmap = pgen2.simulator.fmap;
					res = new PolyGeneralizationResult(g2,fmap,GlobalState.getReMap());
				} catch (Throwable z) {
				    System.err.flush();
					System.exit(1);
					throw z;
				}
			}
			long endTime = System.currentTimeMillis();
			System.out.println(ID.location() + "Polygonal Generalization Time = " + (endTime - startTime) + " ms");
			GlobalState.clearGlobalState();
		}
		return res;
	}
}
