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

abstract public class RationalIntervalType extends NumericIntervalType<RationalType> implements RationalTypeInterface {
	
	@Override
	public final EvaluatableType<RationalType> divide(EvaluatableValue right) {
		RationalTypeInterface rv = (RationalTypeInterface) right;
		return rv.divide2(this);
	}

	@Override
	public final EvaluatableType<RationalType> divide2(RationalType left) {
		RationalType max = getHigh();
		RationalType min = getLow();
		assert(max.signum() == min.signum());
		RationalType p1 = left.divide(max);
		RationalType p2 = left.divide(min);
		return newInterval(p1.min(p2),p1.max(p2));
	}

	@Override
	public final EvaluatableType<RationalType> divide2(RationalIntervalType left) {
		throw new IllegalArgumentException();
	}
	
	
	@Override
	public final Type getType() {
		return NamedType.REAL;
	}

}
