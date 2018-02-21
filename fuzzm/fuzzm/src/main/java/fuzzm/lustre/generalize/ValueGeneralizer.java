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
import fuzzm.lustre.evaluation.Simulator;
import fuzzm.value.hierarchy.EvaluatableType;
import fuzzm.value.hierarchy.InstanceType;

interface ValueGeneralizer<T extends InstanceType<T>> {

	abstract public EvaluatableType<T> generalize(Simulator simulator, SignalName si, EvaluatableType<T> curr, EvaluatableType<T> maxInterval);
	
}
