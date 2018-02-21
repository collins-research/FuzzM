package jfuzz.value.instance;

import java.math.BigInteger;

import jfuzz.value.hierarchy.BooleanType;
import jfuzz.value.hierarchy.EvaluatableType;
import jfuzz.value.hierarchy.IntegerType;
import jfuzz.value.hierarchy.NumericType;
import jfuzz.value.hierarchy.RationalType;
import jkind.util.BigFraction;

public class RationalValue extends RationalType implements RationalValueInterface {
	
	public BigFraction value;
	
	public RationalValue(BigFraction value) {
		this.value = value;
	}

    // divide

	@Override
	public RationalType divide(RationalType right) {
		return ((RationalValueInterface) right).divide2(this);
	}

	@Override
	public RationalType divide2(RationalValue left) {
		return new RationalValue(left.value.divide(value));
	}

	@Override
	public RationalType divide2(RationalInfinity left) {
		return RationalInfinity.newRationalInfinity(left.signum() * signum());
	}

    // multiply

	@Override
	public RationalType multiply(NumericType<RationalType> right) {
		return ((RationalValueInterface) right).multiply2(this);
	}

	@Override
	public RationalType multiply2(RationalValue left) {
		return new RationalValue(left.value.multiply(value));
	}

	@Override
	public RationalType multiply2(RationalInfinity left) {
		return RationalInfinity.newRationalInfinity(left.signum() * signum());
	}

    // plus

	@Override
	public RationalType plus(NumericType<RationalType> right) {
		return ((RationalValueInterface) right).plus2(this);
	}

	@Override
	public RationalType plus2(RationalValue left) {
		return new RationalValue(left.value.add(value));
	}

	@Override
	public RationalType plus2(RationalInfinity left) {
		return left;
	}

    // less

	@Override
	public BooleanType less(NumericType<RationalType> right) {
		return ((RationalValueInterface) right).less2(this);
	}

	@Override
	public BooleanType less2(RationalValue left) {
		return newBooleanType(left.value.compareTo(value) < 0);
	}

	@Override
	public BooleanType less2(RationalInfinity left) {
		return newBooleanType(left.signum() < 0);
	}

    // greater

	@Override
	public BooleanType greater(NumericType<RationalType> right) {
		return ((RationalValueInterface) right).greater2(this);
	}

	@Override
	public BooleanType greater2(RationalValue left) {
		return newBooleanType(left.value.compareTo(value) > 0);
	}

	@Override
	public BooleanType greater2(RationalInfinity left) {
		return newBooleanType(left.signum() > 0);
	}

    // equalop

	@Override
	public BooleanType equalop(NumericType<RationalType> right) {
		return ((RationalValueInterface) right).equalop2(this);
	}

	@Override
	public BooleanType equalop2(RationalValue left) {
		return newBooleanType(left.value.compareTo(value) == 0);
	}

	@Override
	public BooleanType equalop2(RationalInfinity left) {
		return newBooleanType(false);
	}

    // max

	@Override
	public RationalType max(RationalType right) {
		return ((RationalValueInterface) right).max2(this);
	}

	@Override
	public RationalType max2(RationalValue left) {
		return value.compareTo(left.value) > 0 ? this : left;
	}

	@Override
	public RationalType max2(RationalInfinity left) {
		return left.signum() > 0 ? left : this;
	}

    // min

	@Override
	public RationalType min(RationalType right) {
		return ((RationalValueInterface) right).min2(this);
	}

	@Override
	public RationalType min2(RationalValue left) {
		return value.compareTo(left.value) < 0 ? this : left;
	}

	@Override
	public RationalType min2(RationalInfinity left) {
		return left.signum() < 0 ? left : this;
	}

    // unary

	@Override
	public RationalType negate() {
		return new RationalValue(value.negate());
	}

    // auxiliary

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (! (obj instanceof RationalValue))
			return false;
		RationalValue other = (RationalValue) obj;
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
		int sign = value.signum();
		BigFraction half = new BigFraction(BigInteger.ONE,BigInteger.valueOf(2));
		BigFraction absvalue = (sign < 0) ? value.negate() : value;
		BigInteger intvalue = absvalue.add(half).floor();
		intvalue = (sign < 0) ? intvalue.negate() : intvalue;
		return new IntegerValue(intvalue);
	}

	@Override
	public RationalType rationalType() {
		return this;
	}

	@Override
	public BooleanType booleanType() {
		return (value.signum() != 0) ? BooleanValue.TRUE : BooleanValue.FALSE;
	}

	@Override
	public EvaluatableType<RationalType> newInterval(RationalType max) {
		if (this.equals(max)) return this;
		return new RationalInterval(this,max);
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
	public RationalType abs() {
		return value.signum() < 0 ? new RationalValue(value.negate()) : this;
	}
	
	@Override
	public RationalType valueOf(BigInteger arg) {
		return new RationalValue(new BigFraction(arg));
	}

	public BigFraction value() {
		return value;
	}

	@Override
	public BigFraction getValue() {
		return value;
	}

}
