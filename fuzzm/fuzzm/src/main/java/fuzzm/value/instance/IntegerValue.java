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
import fuzzm.value.hierarchy.IntegerType;
import fuzzm.value.hierarchy.NumericType;
import fuzzm.value.hierarchy.RationalType;
import jkind.util.BigFraction;
import jkind.util.Util;

public class IntegerValue extends IntegerType implements IntegerValueInterface {
	
	public BigInteger value;
	
	public IntegerValue(BigInteger value) {
		this.value = value;
	}

    // int_divide

	@Override
	public IntegerType int_divide(IntegerType right) {
		return ((IntegerValueInterface) right).int_divide2(this);
	}

	@Override
	public IntegerType int_divide2(IntegerValue left) {
		return new IntegerValue(Util.smtDivide(left.value,value));
	}

	@Override
	public IntegerType int_divide2(IntegerInfinity left) {
		return IntegerInfinity.newIntegerInfinity(left.signum() * signum());
	}

    // modulus


	@Override
	public EvaluatableType<IntegerType> modulus(IntegerType right) {
		return ((IntegerValueInterface) right).modulus2(this);
	}

	@Override
	public IntegerType modulus2(IntegerValue left) {
		return new IntegerValue(left.value.mod(value));
	}

	@Override
	public EvaluatableType<IntegerType> modulus2(IntegerInfinity left) {
		// JKind uses BigInteger.mod() .. which always returns
		// a non-negative number.
		BigInteger maxvalue = value.abs().subtract(BigInteger.ONE);
		IntegerValue max = new IntegerValue(maxvalue);
		IntegerValue min = new IntegerValue(BigInteger.ZERO);
		return min.newInterval(max);
	}

    // multiply

	@Override
	public IntegerType multiply(NumericType<IntegerType> right) {
		return ((IntegerValueInterface) right).multiply2(this);
	}

	@Override
	public IntegerType multiply2(IntegerValue left) {
		return new IntegerValue(left.value.multiply(value));
	}

	@Override
	public IntegerType multiply2(IntegerInfinity left) {
		return IntegerInfinity.newIntegerInfinity(left.signum() * signum());
	}

    // plus

	@Override
	public IntegerType plus(NumericType<IntegerType> right) {
		return ((IntegerValueInterface) right).plus2(this);
	}

	@Override
	public IntegerType plus2(IntegerValue left) {
		return new IntegerValue(left.value.add(value));
	}

	@Override
	public IntegerType plus2(IntegerInfinity left) {
		return left;
	}

    // less

	@Override
	public BooleanType less(NumericType<IntegerType> right) {
		//if (Debug.enabled) System.out.println(ID.location() + "less(I) : " + this + " < " + right);
		return ((IntegerValueInterface) right).less2(this);
	}

	@Override
	public BooleanType less2(IntegerValue left) {
		BooleanType res = newBooleanType(left.value.compareTo(value) < 0);
		//if (Debug.enabled) System.err.println(ID.location() + "less2 : (" + left + " < " + this + ") = " + res);
		return res;
	}

	@Override
	public BooleanType less2(IntegerInfinity left) {
		return newBooleanType(left.signum() < 0);
	}

    // greater

	@Override
	public BooleanType greater(NumericType<IntegerType> right) {
		//if (Debug.enabled) System.out.println(ID.location() + "greater(I) : " + this + " > " + right);
		return ((IntegerValueInterface) right).greater2(this);
	}

	@Override
	public BooleanType greater2(IntegerValue left) {
		BooleanType res = newBooleanType(left.value.compareTo(value) > 0);
		//if (Debug.enabled) System.err.println(ID.location() + "greater2 : (" + left + " > " + this + ") = " + res);
		return res;
	}

	@Override
	public BooleanType greater2(IntegerInfinity left) {
		return newBooleanType(left.signum() > 0);
	}

    // equalop

	@Override
	public BooleanType equalop(NumericType<IntegerType> right) {
		return ((IntegerValueInterface) right).equalop2(this);
	}

	@Override
	public BooleanType equalop2(IntegerValue left) {
		return newBooleanType(left.value.compareTo(value) == 0);
	}

	@Override
	public BooleanType equalop2(IntegerInfinity right) {
		return newBooleanType(false);
	}

    // max

	@Override
	public IntegerType max(IntegerType right) {
		return ((IntegerValueInterface) right).max2(this);
	}

	@Override
	public IntegerType max2(IntegerValue left) {
		return (left.value.compareTo(value) > 0) ? left : this;
	}

	@Override
	public IntegerType max2(IntegerInfinity left) {
		return left.signum() > 0 ? left : this;
	}

    // min

	@Override
	public IntegerType min(IntegerType right) {
		return ((IntegerValueInterface) right).min2(this);
	}

	@Override
	public IntegerType min2(IntegerValue left) {
		return (left.value.compareTo(value) < 0) ? left : this;
	}

	@Override
	public IntegerType min2(IntegerInfinity left) {
		return left.signum() < 0 ? left : this;
	}

    // unary

	@Override
	public IntegerType negate() {
		return new IntegerValue(value.negate());
	}

    // auxiliary

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (! (obj instanceof IntegerValue))
			return false;
		IntegerValue other = (IntegerValue) obj;
		return value.equals(other.value);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((value == null) ? 0 : value.hashCode());
		return result;
	}

	@Override
	public String toString() {
		return value.toString();
	}

	@Override
	public int signum() {
		return value.signum();
	}

	@Override
	public IntegerType integerType() {
		return this;
	}

	@Override
	public RationalType rationalType() {
		return new RationalValue(new BigFraction(value));
	}

	@Override
	public BooleanType booleanType() {
		return value.signum() != 0 ? BooleanValue.TRUE : BooleanValue.FALSE;
	}

	@Override
	public EvaluatableType<IntegerType> newInterval(IntegerType max) {
		if (this.equals(max)) return this;
		return new IntegerInterval(this,max);
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

	@Override
	public boolean isFinite() {
		return true;
	}

	@Override
	public IntegerType abs() {
		return value.signum() < 0 ? new IntegerValue(value.negate()) : this;
	}

	@Override
	public IntegerType valueOf(BigInteger arg) {
		return new IntegerValue(arg);
	}

	@Override
	public BigFraction getValue() {
		return new BigFraction(value);
	}


}
