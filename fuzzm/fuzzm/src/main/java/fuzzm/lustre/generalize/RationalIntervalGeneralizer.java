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
import fuzzm.value.hierarchy.EvaluatableValueHierarchy;
import fuzzm.value.hierarchy.RationalType;
import fuzzm.value.instance.RationalValue;
import jkind.util.BigFraction;

public class RationalIntervalGeneralizer extends ContinuousIntervalGeneralizer<RationalType> {
	
	public static final RationalType RATIONAL_EPSILON = new RationalValue(new BigFraction(BigInteger.ONE, BigInteger.valueOf(10000)));
	public static final RationalType TWO = new RationalValue(new BigFraction(BigInteger.valueOf(2)));

	@Override
	protected boolean isZero(RationalType x) {
		return ((EvaluatableValueHierarchy)x.abs().minus(RATIONAL_EPSILON)).signum() < 0;
	}

	@Override
	protected RationalType half(EvaluatableValue x) {
		return ((RationalType) x).divide(TWO);
	}

}
