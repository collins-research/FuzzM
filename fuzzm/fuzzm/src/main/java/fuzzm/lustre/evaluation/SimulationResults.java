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

abstract public class SimulationResults {
	abstract public SimulationResults and(EvaluatableValue result);
	abstract public boolean isSatisfactory();
	abstract public BooleanTypeInterface result();
	@Override
	abstract public String toString();
}
