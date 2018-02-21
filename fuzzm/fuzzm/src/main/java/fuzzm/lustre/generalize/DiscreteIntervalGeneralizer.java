/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.lustre.generalize;

import fuzzm.lustre.SignalName;
import fuzzm.lustre.evaluation.ConcreteSimulationResults;
import fuzzm.lustre.evaluation.SimulationResults;
import fuzzm.lustre.evaluation.Simulator;
import fuzzm.value.hierarchy.EvaluatableType;
import fuzzm.value.hierarchy.InstanceType;

public class DiscreteIntervalGeneralizer<T extends InstanceType<T>> implements ValueGeneralizer<T> {
	
	private static final SimulationResults TRUE = new ConcreteSimulationResults();

	public EvaluatableType<T> generalize(Simulator simulator, SignalName si, EvaluatableType<T> curr, EvaluatableType<T> maxInterval) {
		if (simulator.isConsistent(si,maxInterval,TRUE).isSatisfactory()) {
			return maxInterval;
		}
		return curr;
	}

}
