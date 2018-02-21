package jfuzz.value.instance;

import java.math.BigInteger;
import java.util.HashMap;
import java.util.Map;

import jfuzz.poly.PolyBase;
import jfuzz.poly.PolyBool;
import jfuzz.poly.VariableID;
import jfuzz.value.hierarchy.BooleanType;
import jfuzz.value.hierarchy.EvaluatableType;
import jfuzz.value.hierarchy.IntegerType;
import jfuzz.value.hierarchy.NumericType;
import jfuzz.value.hierarchy.RationalType;
import jkind.util.BigFraction;

public class PolyValue extends IntegerType implements PolyValueInterface {

	PolyBase poly;
	
	public PolyValue(VariableID vid) {
		Map<VariableID,BigFraction> newCoefs = new HashMap<VariableID,BigFraction>();
		newCoefs.put(vid, BigFraction.ONE);
		poly = new PolyBase(newCoefs);
	}
	
	public PolyValue(PolyBase poly) {
		this.poly = poly;
	}
	
	@Override
	public IntegerType int_divide(IntegerType right) {
		if (right instanceof IntegerValue) return int_divide2((IntegerValue) right);
		if (right instanceof IntegerInfinity) return int_divide2((IntegerInfinity) right);
		return ((PolyValueInterface) right).int_divide2(this);
	}
	
	@Override
	public IntegerType int_divide2(IntegerValue left) {
		//PolyBase leftPoly = new PolyBase(new BigFraction(left.value));
		BigFraction c = new BigFraction(left.value);
		PolyBase res = this.poly.divide(c);
		return new PolyValue(res);
	}

	@Override
	public IntegerType int_divide2(IntegerInfinity left) {
		return left;
	}

	@Override
	public IntegerType multiply(NumericType<IntegerType> right) {
		if (right instanceof IntegerValue) return multiply2((IntegerValue) right);
		if (right instanceof IntegerInfinity) return multiply2((IntegerInfinity) right);
		return ((PolyValueInterface) right).multiply2(this);
	}

	@Override
	public IntegerType multiply2(IntegerValue left) {
		//PolyBase leftPoly = new PolyBase(new BigFraction(left.value));
		BigFraction c = new BigFraction(left.value);
		PolyBase res = this.poly.multiply(c);
		return new PolyValue(res);
	}

	@Override
	public IntegerType multiply2(IntegerInfinity left) {
		return left;
	}

	@Override
	public IntegerType multiply2(PolyValue left) {
		if (this.poly.isConstant()) {
			return new PolyValue(left.poly.multiply(this.poly.getConstant()));
		} else if (left.poly.isConstant()) {
			return new PolyValue(this.poly.multiply(left.poly.getConstant()));			
		} else {
			throw new IllegalArgumentException("Non-Linear Multiplication");
		}
	}

	@Override
	public IntegerType negate() {
		PolyBase res = this.poly.negate();
		return new PolyValue(res);
	}

	@Override
	public boolean equals(Object x) {
		return poly.equals(x);
	}

	@Override
	public String toString() {
		return poly.toString();
	}

	@Override
	public IntegerType plus(NumericType<IntegerType> right) {
		if (right instanceof IntegerValue) return plus2((IntegerValue) right);
		if (right instanceof IntegerInfinity) return plus2((IntegerInfinity) right);
		return ((PolyValueInterface) right).plus2(this);
	}
	
	@Override
	public IntegerType plus2(IntegerValue left) {
		PolyBase leftPoly = new PolyBase(new BigFraction(left.value));
		PolyBase res = leftPoly.add(this.poly);
		return new PolyValue(res);
	}

	@Override
	public IntegerType plus2(IntegerInfinity left) {
		return left;
	}
	
	@Override
	public IntegerType plus2(PolyValue left) {
		PolyBase leftPoly = left.poly;
		PolyBase res = leftPoly.add(this.poly);
		return new PolyValue(res);
	}

	@Override
	public BooleanType less2(IntegerValue left) {
		PolyBase rhs = this.poly;
		//if (Debug.enabled) System.out.println(ID.location() + "less2 : " + left + " < " + rhs);
		rhs = rhs.subtract(new BigFraction(left.value));
		return new PolyBooleanValue(PolyBool.greater0(rhs));
	}

	@Override
	public BooleanType less2(IntegerInfinity left) {
		return left.signum() > 0 ? BooleanValue.FALSE : BooleanValue.TRUE;
	}

	@Override
	public BooleanType less2(PolyValue left) {
		PolyBase leftPoly = left.poly;
		PolyBase rightPoly = this.poly;
		PolyBase lhs = leftPoly.subtract(rightPoly);
		return new PolyBooleanValue(PolyBool.less0(lhs));
	}

	@Override
	public BooleanType less(NumericType<IntegerType> right) {
		//if (Debug.enabled) System.out.println(ID.location() + "less(P) : " + this + " < " + right);
		if (right instanceof IntegerValue) return greater2((IntegerValue) right);
		if (right instanceof IntegerInfinity) return greater2((IntegerInfinity) right);
		return ((PolyValueInterface) right).less2(this);
	}

	@Override
	public BooleanType greater2(IntegerValue left) {
		PolyBase rhs = this.poly;
		//if (Debug.enabled) System.out.println(ID.location() + "greater2 : " + left + " > " + rhs);
		rhs = rhs.subtract(new BigFraction(left.value));
		return new PolyBooleanValue(PolyBool.less0(rhs));
	}

	@Override
	public BooleanType greater2(IntegerInfinity left) {
		return left.signum() > 0 ? BooleanValue.TRUE : BooleanValue.FALSE;
	}

	@Override
	public BooleanType greater2(PolyValue left) {
		PolyBase leftPoly = left.poly;
		PolyBase rightPoly = this.poly;
		PolyBase lhs = leftPoly.subtract(rightPoly);
		return new PolyBooleanValue(PolyBool.greater0(lhs));
	}

	@Override
	public BooleanType greater(NumericType<IntegerType> right) {
		//if (Debug.enabled) System.out.println(ID.location() + "greater(P) : " + this + " > " + right);
		if (right instanceof IntegerValue) return less2((IntegerValue) right);
		if (right instanceof IntegerInfinity) return less2((IntegerInfinity) right);
		return ((PolyValueInterface) right).greater2(this);
	}

	@Override
	public BooleanType equalop(NumericType<IntegerType> right) {
		if (right instanceof IntegerValue) return equalop2((IntegerValue) right);
		if (right instanceof IntegerInfinity) return equalop2((IntegerInfinity) right);
		return ((PolyValueInterface) right).equalop2(this);
	}

	@Override
	public BooleanType equalop2(IntegerValue left) {
		PolyBase myPoly = this.poly;
		if(myPoly.isConstant()){
			if(myPoly.getConstant().equals(new BigFraction(left.value))){
				return BooleanValue.TRUE;
			}
		}
		return BooleanValue.FALSE;
	}

	@Override
	public BooleanType equalop2(IntegerInfinity left) {
		return BooleanValue.FALSE;
	}

	@Override
	public BooleanType equalop2(PolyValue left) {
		return new PolyBooleanValue(PolyBool.equal0(this.poly.subtract(left.poly)));
	}

	// Unimplemented methods ..	
	
	@Override
	public BigFraction getValue() {
		// TODO Auto-generated method stub
		throw new IllegalArgumentException();
	}

	@Override
	public IntegerType modulus2(IntegerValue left) {
		// TODO Auto-generated method stub
		throw new IllegalArgumentException();
	}

	@Override
	public EvaluatableType<IntegerType> modulus2(IntegerInfinity left) {
		// TODO Auto-generated method stub
		throw new IllegalArgumentException();
	}

	@Override
	public IntegerType max2(IntegerValue left) {
		// TODO Auto-generated method stub
		throw new IllegalArgumentException();
	}

	@Override
	public IntegerType max2(IntegerInfinity left) {
		// TODO Auto-generated method stub
		throw new IllegalArgumentException();
	}

	@Override
	public IntegerType min2(IntegerValue left) {
		// TODO Auto-generated method stub
		throw new IllegalArgumentException();
	}

	@Override
	public IntegerType min2(IntegerInfinity left) {
		// TODO Auto-generated method stub
		throw new IllegalArgumentException();
	}

	@Override
	public IntegerType int_divide2(PolyValue left) {
		// TODO Auto-generated method stub
		throw new IllegalArgumentException();
	}

	@Override
	public IntegerType modulus2(PolyValue left) {
		// TODO Auto-generated method stub
		throw new IllegalArgumentException();
	}

	@Override
	public IntegerType max2(PolyValue left) {
		// TODO Auto-generated method stub
		throw new IllegalArgumentException();
	}

	@Override
	public IntegerType min2(PolyValue left) {
		// TODO Auto-generated method stub
		throw new IllegalArgumentException();
	}

	@Override
	public EvaluatableType<IntegerType> modulus(IntegerType right) {
		// TODO Auto-generated method stub
		throw new IllegalArgumentException();
	}

	@Override
	public EvaluatableType<IntegerType> newInterval(IntegerType max) {
		// TODO Auto-generated method stub
		throw new IllegalArgumentException();
	}

	@Override
	public IntegerType abs() {
		// TODO Auto-generated method stub
		throw new IllegalArgumentException();
	}

	@Override
	public IntegerType valueOf(BigInteger arg) {
		// TODO Auto-generated method stub
		throw new IllegalArgumentException();
	}

	@Override
	public IntegerType max(IntegerType base) {
		// TODO Auto-generated method stub
		throw new IllegalArgumentException();
	}

	@Override
	public IntegerType min(IntegerType base) {
		// TODO Auto-generated method stub
		throw new IllegalArgumentException();
	}

	@Override
	public boolean isFinite() {
		// TODO Auto-generated method stub
		throw new IllegalArgumentException();
	}

	@Override
	public EvaluatableType<IntegerType> integerType() {
		// TODO Auto-generated method stub
		throw new IllegalArgumentException();
	}

	@Override
	public EvaluatableType<RationalType> rationalType() {
		// TODO Auto-generated method stub
		throw new IllegalArgumentException();
	}

	@Override
	public EvaluatableType<BooleanType> booleanType() {
		// TODO Auto-generated method stub
		throw new IllegalArgumentException();
	}

	@Override
	public int hashCode() {
		// TODO Auto-generated method stub
		throw new IllegalArgumentException();
	}

	@Override
	public int signum() {
		// TODO Auto-generated method stub
		throw new IllegalArgumentException();
	}

	@Override
	public IntegerType newIntegerType(BigInteger value) {
		// TODO Auto-generated method stub
		throw new IllegalArgumentException();
	}

	@Override
	public RationalType newRationalType(BigFraction value) {
		// TODO Auto-generated method stub
		throw new IllegalArgumentException();
	}

	@Override
	public BooleanType newBooleanType(boolean value) {
		// TODO Auto-generated method stub
		throw new IllegalArgumentException();
	}

	@Override
	public EvaluatableType<BooleanType> newBooleanInterval() {
		// TODO Auto-generated method stub
		throw new IllegalArgumentException();
	}

}
