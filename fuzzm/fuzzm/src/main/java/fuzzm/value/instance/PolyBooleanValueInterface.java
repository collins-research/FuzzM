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

public interface PolyBooleanValueInterface extends BooleanValueInterface {

	EvaluatableType<BooleanType> equalop2(PolyBooleanValue left);
	EvaluatableType<BooleanType> and2(PolyBooleanValue left);
	EvaluatableType<BooleanType> or2(PolyBooleanValue right);

}
