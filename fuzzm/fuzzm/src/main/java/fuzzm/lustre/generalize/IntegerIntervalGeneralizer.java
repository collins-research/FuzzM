/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.lustre.generalize;

import java.math.BigInteger;

import fuzzm.value.hierarchy.EvaluatableValue;
import fuzzm.value.hierarchy.IntegerType;
import fuzzm.value.instance.IntegerValue;

public class IntegerIntervalGeneralizer extends ContinuousIntervalGeneralizer<IntegerType> {

	@Override
	protected boolean isZero(IntegerType x) {
		boolean res = (x.signum() == 0);
		//System.out.println(ID.location() + "(" + x + " == 0) = " + res);		
		return res;
	}

	@Override
	protected IntegerType half(EvaluatableValue x) {
		IntegerValue two = new IntegerValue(BigInteger.valueOf(2));
		IntegerType res = (IntegerType) x;
		int sign = res.signum();
		res = res.abs().int_divide(two);
		res = (sign < 0) ? res.negate() : res;
		//System.out.println(ID.location() + "1/2 of " + x + " is " + res);		
		return res;
	}

}
