package jfuzz.value.instance;

import java.math.BigInteger;

import jfuzz.value.hierarchy.BooleanType;
import jfuzz.value.hierarchy.EvaluatableType;
import jfuzz.value.hierarchy.IntegerType;
import jfuzz.value.hierarchy.NumericType;
import jfuzz.value.hierarchy.RationalType;
import jkind.util.BigFraction;

public final class RationalInfinity extends RationalType implements RationalValueInterface {

	public static final RationalInfinity POSITIVE_INFINITY = new RationalInfinity();
	public static final RationalInfinity NEGATIVE_INFINITY = new RationalInfinity();
	
	private RationalInfinity() {		
	}
	
	public static RationalType newRationalInfinity(int sign) {
		if (sign == 0) return new RationalValue(BigFraction.ZERO);
		return (sign < 0) ? NEGATIVE_INFINITY : POSITIVE_INFINITY;
	}

    // divide

	@Override
	public RationalType divide(RationalType right) {
		return ((RationalValueInterface) right).divide2(this);
	}

	@Override
	public RationalType divide2(RationalValue left) {
		throw new IllegalArgumentException();
	}

	@Override
	public RationalType divide2(RationalInfinity left) {
		throw new IllegalArgumentException();
	}

    // multiply

	@Override
	public RationalType multiply(NumericType<RationalType> right) {
		return ((RationalValueInterface) right).multiply2(this);
	}

	@Override
	public RationalType multiply2(RationalValue left) {
		return newRationalInfinity(left.signum() * signum());
	}

	@Override
	public RationalType multiply2(RationalInfinity left) {
		return newRationalInfinity(left.signum() * signum());
	}

    // plus

	@Override
	public RationalType plus(NumericType<RationalType> right) {
		return ((RationalValueInterface) right).plus2(this);
	}

	@Override
	public RationalType plus2(RationalValue left) {
		return this;
	}

	@Override
	public RationalType plus2(RationalInfinity left) {
		assert(signum() == left.signum());
		return this;
	}

    // less

	@Override
	public BooleanType less(NumericType<RationalType> right) {
		return ((RationalValueInterface) right).less2(this);
	}

	@Override
	public BooleanType less2(RationalValue left) {
		return newBooleanType(0 < signum());
	}

	@Override
	public BooleanType less2(RationalInfinity left) {
		return newBooleanType(left.signum() < signum());
	}

    // greater

	@Override
	public BooleanType greater(NumericType<RationalType> right) {
		return ((RationalValueInterface) right).greater2(this);
	}

	@Override
	public BooleanType greater2(RationalValue left) {
		return newBooleanType(0 > signum());
	}

	@Override
	public BooleanType greater2(RationalInfinity left) {
		return newBooleanType(left.signum() > signum());
	}

    // equalop

	@Override
	public BooleanType equalop(NumericType<RationalType> right) {
		return ((RationalValueInterface) right).equalop2(this);
	}

	@Override
	public BooleanType equalop2(RationalValue left) {
		return newBooleanType(false);
	}

	@Override
	public BooleanType equalop2(RationalInfinity left) {
		return newBooleanType(left.signum() == signum());
	}

    // max

	@Override
	public RationalType max(RationalType right) {
		return ((RationalValueInterface) right).max2(this);
	}

	@Override
	public RationalType max2(RationalValue left) {
		return signum() > 0 ? this : left;
	}

	@Override
	public RationalType max2(RationalInfinity left) {
		return signum() > left.signum() ? this : left;
	}

    // min

	@Override
	public RationalType min(RationalType right) {
		return ((RationalValueInterface) right).min2(this);
	}

	@Override
	public RationalType min2(RationalValue left) {
		return signum() < 0 ? this : left;
	}

	@Override
	public RationalType min2(RationalInfinity left) {
		return signum() < left.signum() ? this : left;
	}

    // unary

	@Override
	public RationalType negate() {
		return newRationalInfinity(- signum());
	}

    // auxiliary

	@Override
	public EvaluatableType<RationalType> newInterval(RationalType max) {
		if (this.equals(max)) return this;
		return new RationalInterval(this,max);
	}

	@Override
	public boolean equals(Object x) {
		return (this == x);
	}

	@Override
	public int hashCode() {
		return signum() < 0 ? -13 : 13;
	}

	@Override
	public String toString() {
		return "" + signum() + ".0/0.0";
	}

	@Override
	public int signum() {
		return (this == POSITIVE_INFINITY) ? +1 : -1;
	}

	@Override
	public IntegerType integerType() {
		return signum() > 0 ? IntegerInfinity.POSITIVE_INFINITY : IntegerInfinity.NEGATIVE_INFINITY;
	}

	@Override
	public RationalType rationalType() {
		return this;
	}

	@Override
	public BooleanType booleanType() {
		return (signum() > 0) ? BooleanValue.TRUE : BooleanValue.FALSE;
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
		return false;
	}

	@Override
	public RationalType abs() {
		return POSITIVE_INFINITY;
	}

	@Override
	public RationalType valueOf(BigInteger arg) {
		return new RationalValue(new BigFraction(arg));
	}

	@Override
	public BigFraction getValue() {
		// TODO Auto-generated method stub
		throw new IllegalArgumentException();
	}

}
