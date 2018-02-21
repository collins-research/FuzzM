package jfuzz.value.instance;

import java.math.BigInteger;

import jfuzz.value.hierarchy.BooleanType;
import jfuzz.value.hierarchy.EvaluatableType;
import jfuzz.value.hierarchy.IntegerType;
import jfuzz.value.hierarchy.NumericType;
import jfuzz.value.hierarchy.RationalType;
import jkind.util.BigFraction;

public class IntegerInfinity extends IntegerType implements IntegerValueInterface {

	public static final IntegerInfinity POSITIVE_INFINITY = new IntegerInfinity();
	public static final IntegerInfinity NEGATIVE_INFINITY = new IntegerInfinity();
	
	private IntegerInfinity() {		
	}

	public static IntegerType newIntegerInfinity(int sign) {
		if (sign == 0) return new IntegerValue(BigInteger.ZERO);
		return sign < 0 ? NEGATIVE_INFINITY : POSITIVE_INFINITY;
	}
	
    // int_divide

	@Override
	public IntegerType int_divide(IntegerType right) {
		return ((IntegerValueInterface) right).int_divide2(this);
	}

	@Override
	public IntegerType int_divide2(IntegerValue left) {
		// int/infinity;
		throw new IllegalArgumentException();
	}

	@Override
	public IntegerType int_divide2(IntegerInfinity left) {
		// infinity/infinity
		throw new IllegalArgumentException();
	}

    // modulus

	@Override
	public EvaluatableType<IntegerType> modulus(IntegerType right) {
		return ((IntegerValueInterface) right).modulus2(this);
	}

	@Override
	public IntegerType modulus2(IntegerValue left) {
		// int % infinity;
		throw new IllegalArgumentException();
	}

	@Override
	public EvaluatableType<IntegerType> modulus2(IntegerInfinity left) {
		// infinity % infinity
		throw new IllegalArgumentException();
	}

    // multiply

	@Override
	public IntegerType multiply(NumericType<IntegerType> right) {
		return ((IntegerValueInterface) right).multiply2(this);
	}

	@Override
	public IntegerType multiply2(IntegerValue left) {
		return newIntegerInfinity(signum() * left.signum());
	}

	@Override
	public IntegerType multiply2(IntegerInfinity left) {
		return newIntegerInfinity(signum() * left.signum());
	}

    // plus

	@Override
	public IntegerType plus(NumericType<IntegerType> right) {
		return ((IntegerValueInterface) right).plus2(this);
	}

	@Override
	public IntegerType plus2(IntegerValue left) {
		return this;
	}

	@Override
	public IntegerType plus2(IntegerInfinity left) {
		assert(left.signum() == signum());
		return this;
	}

    // less

	@Override
	public BooleanType less(NumericType<IntegerType> right) {
		return ((IntegerValueInterface) right).less2(this);
	}

	@Override
	public BooleanType less2(IntegerValue left) {
		return newBooleanType(0 < signum());
	}

	@Override
	public BooleanType less2(IntegerInfinity left) {
		return newBooleanType(left.signum() < signum());
	}

    // greater

	@Override
	public BooleanType greater(NumericType<IntegerType> right) {
		return ((IntegerValueInterface) right).greater2(this);
	}

	@Override
	public BooleanType greater2(IntegerValue left) {
		return newBooleanType(0 > signum());
	}

	@Override
	public BooleanType greater2(IntegerInfinity left) {
		return newBooleanType(left.signum() > signum());
	}

    // equalop

	@Override
	public BooleanType equalop(NumericType<IntegerType> right) {
		return ((IntegerValueInterface) right).equalop2(this);
	}

	@Override
	public BooleanType equalop2(IntegerValue left) {
		return newBooleanType(false);
	}

	@Override
	public BooleanType equalop2(IntegerInfinity left) {
		return newBooleanType(left.signum() == signum());
	}

    // max

	@Override
	public IntegerType max(IntegerType right) {
		return ((IntegerValueInterface) right).max2(this);
	}

	@Override
	public IntegerType max2(IntegerValue left) {
		return signum() > 0  ? this :left;
	}

	@Override
	public IntegerType max2(IntegerInfinity left) {
		return signum() > left.signum() ? this : left;
	}

    // min

	@Override
	public IntegerType min(IntegerType right) {
		return ((IntegerValueInterface) right).min2(this);
	}

	@Override
	public IntegerType min2(IntegerValue left) {
		return signum() < 0 ? this : left;
	}

	@Override
	public IntegerType min2(IntegerInfinity left) {
		return signum() < left.signum() ? this : left;
	}

    // unary

	@Override
	public IntegerType negate() {
		return newIntegerInfinity(- signum());
	}

    // auxiliary

	@Override
	public EvaluatableType<IntegerType> newInterval(IntegerType max) {
		if (this.equals(max)) return this;
		return new IntegerInterval(this,max);
	}

	@Override
	public boolean equals(Object obj) {
		return (this == obj);
	}

	@Override
	public int hashCode() {
		return signum() < 0 ? -23 : 23;
	}

	@Override
	public String toString() {
		return "" + signum() + "/0";
	}

	@Override
	public int signum() {
		return (this == POSITIVE_INFINITY) ? +1 : -1;
	}

	@Override
	public IntegerType integerType() {
		return this;
	}

	@Override
	public RationalType rationalType() {
		return (signum() < 0) ? RationalInfinity.NEGATIVE_INFINITY : RationalInfinity.POSITIVE_INFINITY;
	}

	@Override
	public BooleanType booleanType() {
		return (signum() < 0) ? BooleanValue.FALSE : BooleanValue.TRUE;
	}

	@Override
	public EvaluatableType<BooleanType> newBooleanInterval() {
		return BooleanInterval.ARBITRARY;
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
	public boolean isFinite() {
		return false;
	}

	@Override
	public IntegerType abs() {
		return POSITIVE_INFINITY;
	}

	@Override
	public IntegerType valueOf(BigInteger arg) {
		return new IntegerValue(arg);
	}

	@Override
	public BigFraction getValue() {
		// TODO Auto-generated method stub
		throw new IllegalArgumentException();
	}

}
