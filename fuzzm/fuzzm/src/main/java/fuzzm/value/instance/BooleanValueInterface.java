/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.value.instance;

import fuzzm.value.hierarchy.BooleanType;
import fuzzm.value.hierarchy.EvaluatableType;
import fuzzm.value.hierarchy.EvaluatableValue;

public interface BooleanValueInterface {

	EvaluatableType<BooleanType> not();
	
	EvaluatableType<BooleanType> equalop(EvaluatableValue right);
	EvaluatableType<BooleanType> equalop2(BooleanValue left);
	EvaluatableType<BooleanType> equalop2(BooleanInterval left);

	EvaluatableType<BooleanType> and(EvaluatableValue right);
	EvaluatableType<BooleanType> and2(BooleanValue left);
	EvaluatableType<BooleanType> and2(BooleanInterval left);

	EvaluatableType<BooleanType> or(EvaluatableValue right);
	EvaluatableType<BooleanType> or2(BooleanValue left);
	EvaluatableType<BooleanType> or2(BooleanInterval left);

}
