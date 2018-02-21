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

public class ConcreteSimulationResults extends SimulationResults {

	EvaluatableValue result;
	
	public ConcreteSimulationResults() {
		result = BooleanValue.TRUE;
	}
	
	private ConcreteSimulationResults(EvaluatableValue result) {
		this.result = result;
	}
	
	@Override
	public ConcreteSimulationResults and(EvaluatableValue result) {
		return new ConcreteSimulationResults(this.result.and(result));
	}

	@Override
	public boolean isSatisfactory() {
		return ((BooleanTypeInterface) result).isAlwaysTrue();
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
