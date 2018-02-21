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

import fuzzm.value.hierarchy.BooleanIntervalType;
import fuzzm.value.hierarchy.BooleanType;
import fuzzm.value.hierarchy.EvaluatableType;
import fuzzm.value.hierarchy.EvaluatableValue;
import fuzzm.value.hierarchy.EvaluatableValueHierarchy;
import fuzzm.value.hierarchy.InstanceType;
import fuzzm.value.hierarchy.IntegerType;
import fuzzm.value.hierarchy.RationalType;
import jkind.util.BigFraction;

public class BooleanInterval extends BooleanIntervalType implements BooleanValueInterface {

	public static final BooleanInterval ARBITRARY = new BooleanInterval();
	
    // and

	@Override
	public EvaluatableType<BooleanType> and(EvaluatableValue right) {
		return ((BooleanValueInterface) right).and2(this);
	}

	@Override
	public EvaluatableType<BooleanType> and2(BooleanValue left) {
		return (left == BooleanValue.FALSE) ? left : ARBITRARY;
	}

	@Override
	public EvaluatableType<BooleanType> and2(BooleanInterval left) {
		return ARBITRARY;
	}

    // or

	@Override
	public EvaluatableType<BooleanType> or(EvaluatableValue right) {
		return ((BooleanValueInterface) right).or2(this);
	}

	@Override
	public EvaluatableType<BooleanType> or2(BooleanValue left) {
		return (left == BooleanValue.TRUE) ? left : ARBITRARY;
	}

	@Override
	public EvaluatableType<BooleanType> or2(BooleanInterval left) {
		return ARBITRARY;
	}

    // equalop

	@Override
	public EvaluatableType<BooleanType> equalop(EvaluatableValue right) {
		return ((BooleanValueInterface) right).equalop2(this);
	}

	@Override
	public EvaluatableType<BooleanType> equalop2(BooleanValue left) {
		return ARBITRARY;
	}

	@Override
	public EvaluatableType<BooleanType> equalop2(BooleanInterval left) {
		return ARBITRARY;
	}

    // ite

	@Override
	public EvaluatableValue ite(EvaluatableValue left, EvaluatableValue right) {
		return ((EvaluatableValueHierarchy) left).join(right);
	}

    // unary

	@Override
	public EvaluatableType<BooleanType> not() {
		return this;
	}

    // auxiliary

	@Override
	public BooleanType getLow() {
		return BooleanValue.FALSE;
	}

	@Override
	public BooleanType getHigh() {
		return BooleanValue.TRUE;
	}

	@Override
	public EvaluatableType<BooleanType> newInterval(InstanceType<BooleanType> min, InstanceType<BooleanType> max) {
		if (min.equals(max)) return min;
		return ARBITRARY;
	}

	@Override
	public boolean equals(Object x) {
		return (this == x);
	}

	@Override
	public int hashCode() {
		return 19;
	}

	@Override
	public String toString() {
		return "[F,T]";
	}

	@Override
	public boolean isTrue() {
		return false;
	}

	@Override
	public boolean isFalse() {
		return false;
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
		return value ? BooleanValue.TRUE : BooleanValue.FALSE;
	}

	@Override
	public EvaluatableType<BooleanType> newBooleanInterval() {
		return this;
	}

}
