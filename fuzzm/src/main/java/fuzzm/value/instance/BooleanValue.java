package jfuzz.value.instance;

import java.math.BigInteger;

import jfuzz.value.hierarchy.BooleanType;
import jfuzz.value.hierarchy.EvaluatableType;
import jfuzz.value.hierarchy.EvaluatableValue;
import jfuzz.value.hierarchy.IntegerType;
import jfuzz.value.hierarchy.RationalType;
import jkind.util.BigFraction;

public class BooleanValue extends BooleanType implements BooleanValueInterface {

	public static final BooleanValue TRUE  = new BooleanValue();
	public static final BooleanValue FALSE = new BooleanValue();

	protected BooleanValue() {
	}
	
	// and
	
	@Override
	public EvaluatableType<BooleanType> and(EvaluatableValue right) {
		return ((BooleanValueInterface) right).and2(this);
	}
	
	@Override
	public EvaluatableType<BooleanType> and2(BooleanValue left) {
		return (left == TRUE) && (this == TRUE) ? TRUE : FALSE;
	}
	
	@Override
	public EvaluatableType<BooleanType> and2(BooleanInterval left) {
		return (this == TRUE) ? left : FALSE;
	}

	// or
	
	@Override
	public EvaluatableType<BooleanType> or(EvaluatableValue right) {
		return ((BooleanValueInterface) right).or2(this);
	}
	
	@Override
	public BooleanType or2(BooleanValue left) {
		return ((left == TRUE) || (this == TRUE)) ? TRUE : FALSE;
	}

	@Override
	public EvaluatableType<BooleanType> or2(BooleanInterval left) {
		return (this == TRUE) ? TRUE : left;
	}

	// equalop

	@Override
	public EvaluatableType<BooleanType> equalop(EvaluatableValue right) {
		return ((BooleanValueInterface) right).equalop2(this);
	}
	
	@Override
	public BooleanType equalop2(BooleanValue left) {
		return (this == left) ? TRUE : FALSE;
	}

	@Override
	public EvaluatableType<BooleanType> equalop2(BooleanInterval left) {
		return left;
	}

    // max

	@Override
	public BooleanType max(BooleanType right) {
		return (((BooleanValue) right) == TRUE) ? right : this;
	}

    // min

	@Override
	public BooleanType min(BooleanType right) {
		return (((BooleanValue) right) == FALSE) ? right : this;
	}

	// ite
	@Override
	public EvaluatableValue ite(EvaluatableValue left, EvaluatableValue right) {
		return (this == TRUE) ? left : right;
	}

	// unary
	
	@Override
	public BooleanType not() {
		return (this == TRUE) ? FALSE : TRUE;
	}
	
	// auxiliary
	
	@Override
	public boolean isTrue() {
		return this == TRUE;
	}

	@Override
	public boolean isFalse() {
		return this == FALSE;
	}

	@Override
	public String toString() {
		return (this == TRUE) ? "T" : "F";
	}

	@Override
	public int signum() {
		return (this == TRUE) ? +1 : 0;
	}

	@Override
	public IntegerType integerType() {
		return (this == TRUE) ? new IntegerValue(BigInteger.ONE) : new IntegerValue(BigInteger.ZERO);
	}

	@Override
	public RationalType rationalType() {
		return (this == TRUE) ? new RationalValue(BigFraction.ONE) : new RationalValue(BigFraction.ZERO);
	}

	@Override
	public BooleanType booleanType() {
		return this;
	}

	@Override
	public boolean equals(Object x) {
		return (x == this);
	}

	@Override
	public int hashCode() {
		return (this == TRUE) ? 13 : 7 ;
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
	public BigFraction getValue() {
		return (this == TRUE) ? BigFraction.ONE : BigFraction.ZERO;
	}

}
