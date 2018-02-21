package jfuzz.value.instance;

import java.math.BigInteger;

import jfuzz.poly.PolyBool;
import jfuzz.value.hierarchy.BooleanType;
import jfuzz.value.hierarchy.EvaluatableType;
import jfuzz.value.hierarchy.EvaluatableValue;
import jfuzz.value.hierarchy.EvaluatableValueHierarchy;
import jfuzz.value.hierarchy.IntegerType;
import jfuzz.value.hierarchy.RationalType;
import jkind.util.BigFraction;

public class PolyBooleanValue extends BooleanType implements PolyBooleanValueInterface {

	public PolyBool value;
	
	public PolyBooleanValue(PolyBool value) {
		this.value = value;
	}
	
	// not()
	
	@Override
	public EvaluatableType<BooleanType> not() {
		return new PolyBooleanValue(value.not());
	}

	// and()
	
	@Override
	public EvaluatableType<BooleanType> and(EvaluatableValue right) {
		if (right instanceof BooleanValue) return and2((BooleanValue) right);
		if (right instanceof BooleanInterval) return and2((BooleanInterval) right);
		return ((PolyBooleanValueInterface) right).and2(this);
	}

	@Override
	public EvaluatableType<BooleanType> and2(BooleanValue left) {
		return (left == BooleanValue.TRUE) ? this : left;
	}

	@Override
	public EvaluatableType<BooleanType> and2(BooleanInterval left) {
		return left;
	}

	@Override
	public EvaluatableType<BooleanType> and2(PolyBooleanValue left) {
		return new PolyBooleanValue(this.value.and(left.value));
	}

	// or()

	@Override
	public EvaluatableType<BooleanType> or(EvaluatableValue right) {
		if (right instanceof BooleanValue) return or2((BooleanValue) right);
		if (right instanceof BooleanInterval) return or2((BooleanInterval) right);
		return ((PolyBooleanValueInterface) right).or2(this);
	}

	@Override
	public EvaluatableType<BooleanType> or2(BooleanValue left) {
		return (left == BooleanValue.FALSE) ? this : left;
	}

	@Override
	public EvaluatableType<BooleanType> or2(BooleanInterval left) {
		return left;
	}

	@Override
	public EvaluatableType<BooleanType> or2(PolyBooleanValue left) {
		return new PolyBooleanValue(this.value.or(left.value));
	}

	// equal()
	
	@Override
	public EvaluatableType<BooleanType> equalop(EvaluatableValue right) {
		if (right instanceof BooleanValue) return equalop2((BooleanValue) right);
		if (right instanceof BooleanInterval) return equalop2((BooleanInterval) right);
		return ((PolyBooleanValueInterface) right).equalop2(this);
	}

	@Override
	public EvaluatableType<BooleanType> equalop2(BooleanValue left) {
		return (left == BooleanValue.TRUE) ? this : new PolyBooleanValue(this.value.not());
	}

	@Override
	public EvaluatableType<BooleanType> equalop2(BooleanInterval left) {
		return left;
	}

	@Override
	public EvaluatableType<BooleanType> equalop2(PolyBooleanValue left) {
		return new PolyBooleanValue(this.value.iff(left.value));
	}

	// ite()
	//
	// Yeah .. this will be fun.  For now I guess it is just a join.
	// Unless they are boolean.
	//
	@Override
	public EvaluatableValue ite(EvaluatableValue left, EvaluatableValue right) {
		if (left instanceof BooleanType)  {
			return and(left).or(not().and(right));
		}
		// TODO: what we need to do is "promote" the condition .. but that really
		// only makes sense if we know "for sure" that we need the result of this
		// computation .. which is to say: the simulation should *not* be event
		// based.  It should be a recursive decent evaluation.  Everything old is
		// new again.
		return ((EvaluatableValueHierarchy) left).join(right);
	}
	
	// auxiliary
	
	@Override
	public boolean isTrue() {
		return value.isTrue();
	}

	@Override
	public boolean isFalse() {
		return value.isFalse();
	}

	@Override
	public BooleanType max(BooleanType right) {
		throw new IllegalArgumentException();
	}

	@Override
	public BooleanType min(BooleanType right) {
		throw new IllegalArgumentException();
	}

	@Override
	public boolean isFinite() {
		throw new IllegalArgumentException();
	}

	@Override
	public EvaluatableType<IntegerType> integerType() {
		throw new IllegalArgumentException();
	}

	@Override
	public EvaluatableType<RationalType> rationalType() {
		throw new IllegalArgumentException();
	}

	@Override
	public EvaluatableType<BooleanType> booleanType() {
		return this;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (!( obj instanceof PolyBooleanValue))
			return false;
		PolyBooleanValue other = (PolyBooleanValue) obj;
		return value.equals(other.value);
	}

	@Override
	public int hashCode() {
		return value.hashCode();
	}

	@Override
	public String toString() {
		return value.toString();
	}

	@Override
	public int signum() {
		throw new IllegalArgumentException();
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
		return BooleanInterval.ARBITRARY;
	}

	@Override
	public BigFraction getValue() {
		// TODO Auto-generated method stub
		throw new IllegalArgumentException();
	}

}
