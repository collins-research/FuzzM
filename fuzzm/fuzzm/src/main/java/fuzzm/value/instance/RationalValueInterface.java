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
import fuzzm.value.hierarchy.NumericType;
import fuzzm.value.hierarchy.RationalType;

public interface RationalValueInterface /*extends NumericTypeInterface<RationalType>*/ {

	RationalType divide(RationalType right);
	RationalType divide2(RationalValue left);
	RationalType divide2(RationalInfinity left);

	RationalType plus(NumericType<RationalType> right);
	RationalType plus2(RationalValue left);
	RationalType plus2(RationalInfinity left);

	RationalType multiply(NumericType<RationalType> right);
	RationalType multiply2(RationalValue left);
	RationalType multiply2(RationalInfinity left);

	RationalType max(RationalType right);
	RationalType max2(RationalValue left);
	RationalType max2(RationalInfinity left);

	RationalType min(RationalType right);
	RationalType min2(RationalValue left);
	RationalType min2(RationalInfinity left);

	BooleanType less(NumericType<RationalType> right);
	BooleanType less2(RationalValue left);
	BooleanType less2(RationalInfinity left);

	BooleanType greater(NumericType<RationalType> right);
	BooleanType greater2(RationalValue left);
	BooleanType greater2(RationalInfinity left);

	BooleanType equalop(NumericType<RationalType> right);
	BooleanType equalop2(RationalValue left);
	BooleanType equalop2(RationalInfinity left);

}
