/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.value.instance;

import java.math.BigInteger;

import fuzzm.value.hierarchy.BooleanType;
import fuzzm.value.hierarchy.EvaluatableType;
import fuzzm.value.hierarchy.InstanceType;
import fuzzm.value.hierarchy.IntegerType;
import fuzzm.value.hierarchy.RationalIntervalType;
import fuzzm.value.hierarchy.RationalType;
import jkind.util.BigFraction;

public class RationalInterval extends RationalIntervalType {

	RationalType min;
	RationalType max;

	public static final RationalInterval INFINITE_INTERVAL = new RationalInterval(RationalInfinity.NEGATIVE_INFINITY,RationalInfinity.POSITIVE_INFINITY);
	
	public RationalInterval(RationalType min, RationalType max) {
		this.min = min;
		this.max = max;
	}
	
	public RationalInterval(BigFraction min, BigFraction max) {
		assert(! min.equals(max));
		this.min = new RationalValue(min);
		this.max = new RationalValue(max);
	}
	
	public static EvaluatableType<RationalType> newRationalInterval(InstanceType<RationalType> min, InstanceType<RationalType> max) {
		if (min.equals(max)) return min;
		return new RationalInterval((RationalType) min,(RationalType) max);
	}
	
	@Override
	public EvaluatableType<RationalType> newInterval(InstanceType<RationalType> min, InstanceType<RationalType> max) {
		if (min.equals(max)) {
			return min;
		}
		return new RationalInterval((RationalType) min, (RationalType) max);
	}

	@Override
	public RationalType getLow() {
		return min;
	}

	@Override
	public RationalType getHigh() {
		return max;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (! (obj instanceof RationalInterval))
			return false;
		RationalInterval other = (RationalInterval) obj;
		return max.equals(other.max) && min.equals(other.min);
		
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((max == null) ? 0 : max.hashCode());
		result = prime * result + ((min == null) ? 0 : min.hashCode());
		return result;
	}

	@Override
	public String toString() {
		return "[" + min + "," + max + "]";
	}

	@Override
	public IntegerType newIntegerType(BigInteger value) {
		return new IntegerValue(value);
	}

	@Override
	public RationalType newRationalType(BigFraction value) {
		return new RationalValue(value);
	}

	@Override
	public BooleanType newBooleanType(boolean value) {
		return value ? BooleanValue.TRUE : BooleanValue.FALSE ;
	}

	@Override
	public EvaluatableType<BooleanType> newBooleanInterval() {
		return BooleanInterval.ARBITRARY;
	}

}
