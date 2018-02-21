/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.lustre.evaluation;

import fuzzm.util.Debug;
import fuzzm.util.EvaluatableSignal;
import fuzzm.value.hierarchy.EvaluatableValue;
import fuzzm.value.instance.BooleanValue;
import fuzzm.value.instance.IntegerValue;
import fuzzm.value.instance.RationalValue;
import jkind.lustre.BoolExpr;
import jkind.lustre.IntExpr;
import jkind.lustre.Program;
import jkind.lustre.RealExpr;
import jkind.util.BigFraction;

public class Simulator extends EventBasedSimulator {

	public static Simulator newSimulator(EvaluatableSignal inputs, FunctionLookupEV fns, String property, Program specNode, SimulationResults res) {
		Simulator genSim;
		try { 
 			genSim = new Simulator(inputs,fns,property,specNode,res);
 		} catch (Throwable t) {
 			Debug.setEnabled(true);
 			try {
 				System.err.println("Retry failed Simulation ..");
 				genSim = new Simulator(inputs,fns,property,specNode,res);
 			} catch (Throwable z) {
 				System.err.flush();
 				throw z;
 			}
 		}
		return genSim;
	}
	
	protected Simulator(EvaluatableSignal inputs, FunctionLookupEV fns, String property, Program specNode, SimulationResults res) {
		super(inputs,fns,property,specNode,res);
	}

	@Override
	public EvaluatableValue visit(IntExpr arg0) {
		return new IntegerValue(arg0.value);
	}

	@Override
	public EvaluatableValue visit(RealExpr arg0) {
		return new RationalValue(BigFraction.valueOf(arg0.value));
	}

	@Override
	public EvaluatableValue visit(BoolExpr arg0) {
		return arg0.value ? BooleanValue.TRUE : BooleanValue.FALSE;
	}

	@Override
	public EvaluatableValue trueValue() {
		return BooleanValue.TRUE;
	}

	@Override
	public EvaluatableValue falseValue() {
		return BooleanValue.FALSE;
	}

}
