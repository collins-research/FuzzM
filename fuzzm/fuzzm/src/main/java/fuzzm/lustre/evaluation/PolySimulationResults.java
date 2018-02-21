/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.lustre.evaluation;

import fuzzm.value.hierarchy.BooleanTypeInterface;
import fuzzm.value.hierarchy.EvaluatableValue;
import fuzzm.value.instance.BooleanValue;

public class PolySimulationResults extends SimulationResults {

	public EvaluatableValue result;
	
	public PolySimulationResults() {
		result = BooleanValue.TRUE;
	}
	
	private PolySimulationResults(EvaluatableValue result) {
		this.result = result;
	}
	
	@Override
	public PolySimulationResults and(EvaluatableValue result) {
		EvaluatableValue res = this.result.and(result);
		//if (Debug.isEnabled()) System.out.println(ID.location() + "Accumulated Simulation Results : " + res);
		return new PolySimulationResults(res);
	}

	@Override
	public boolean isSatisfactory() {
		return (! ((BooleanTypeInterface) result).isAlwaysFalse());
	}

	@Override
	public BooleanTypeInterface result() {
		return (BooleanTypeInterface) result;
	}

	@Override
	public String toString() {
		return result.toString();
	}

}
