package jfuzz.lustre.generalize;

import java.util.Collections;
import java.util.List;

import jfuzz.lustre.SignalName;
import jfuzz.lustre.evaluation.FunctionLookupEV;
import jfuzz.lustre.evaluation.PolyFunctionMap;
import jfuzz.poly.PolyBase;
import jfuzz.poly.PolyBool;
import jfuzz.poly.VariableID;
import jfuzz.util.Debug;
import jfuzz.util.EvaluatableSignal;
import jfuzz.util.ID;
import jfuzz.value.hierarchy.BooleanType;
import jfuzz.value.hierarchy.EvaluatableValue;
import jfuzz.value.hierarchy.IntegerType;
import jfuzz.value.hierarchy.RationalType;
import jfuzz.value.poly.BooleanPoly;
import jfuzz.value.poly.GlobalState;
import jfuzz.value.poly.IntegerPoly;
import jfuzz.value.poly.RationalPoly;
import jkind.lustre.Program;
import jkind.util.BigFraction;

public class PolygonalGeneralizer {

	protected final DepthFirstPolyGeneralizer simulator;

	public PolygonalGeneralizer(FunctionLookupEV fev, Program program) {
		this.simulator = new DepthFirstPolyGeneralizer(fev, program.getMainNode());
	}
	
	// TODO: We could, of course, just pass in a poly (rather than hierarchy) type to begin with ..
	private PolyBool generalize(EvaluatableSignal cex, String property) {
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
		PolyBool polyRes = simulator.simulateProperty(state, property);
		polyRes = polyRes.normalize();
		if (Debug.logic()) System.out.println(ID.location() + "Generalization Result : " + polyRes);
		return polyRes;
	}
	
	public static PolyGeneralizationResult generalizeInterface(EvaluatableSignal cex, String property, FunctionLookupEV fns, Program testMain) {
		PolyGeneralizationResult res;
		synchronized (GlobalState.class) {
			long startTime = System.currentTimeMillis();
			try {
				PolygonalGeneralizer pgen2 = new PolygonalGeneralizer(fns,testMain);			
				PolyBool g2 = pgen2.generalize(cex,property);
				PolyFunctionMap fmap = pgen2.simulator.fmap;
				res = new PolyGeneralizationResult(g2,fmap);
			} catch (Throwable t) {
				System.err.println(ID.location() + "Retrying failed PolyGeneralization ..");
				t.printStackTrace();
				Debug.setEnabled(true);
				try {
					PolygonalGeneralizer pgen2 = new PolygonalGeneralizer(fns,testMain);			
					PolyBool g2 = pgen2.generalize(cex,property);
					PolyFunctionMap fmap = pgen2.simulator.fmap;
					res = new PolyGeneralizationResult(g2,fmap);
				} catch (Throwable z) {
					System.err.flush();
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
