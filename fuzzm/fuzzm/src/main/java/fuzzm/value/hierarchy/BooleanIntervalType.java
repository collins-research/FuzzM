/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.value.hierarchy;

import jkind.lustre.NamedType;
import jkind.lustre.Type;

abstract public class BooleanIntervalType extends IntervalType<BooleanType> implements BooleanTypeInterface {

	@Override
	abstract public EvaluatableValue ite(EvaluatableValue left, EvaluatableValue right);
	
	@Override
	abstract public EvaluatableType<BooleanType> not();
	
	@Override
	abstract public EvaluatableType<BooleanType> equalop(EvaluatableValue right);

	@Override
	abstract public EvaluatableType<BooleanType> and(EvaluatableValue right);

	@Override
	abstract public EvaluatableType<BooleanType> or(EvaluatableValue right);
	
	@Override
	public Type getType() {
		return NamedType.BOOL;
	}

}
