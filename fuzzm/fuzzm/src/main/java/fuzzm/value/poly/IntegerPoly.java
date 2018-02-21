/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.value.poly;

import java.math.BigInteger;
import java.util.HashMap;
import java.util.Map;

import fuzzm.poly.AbstractPoly;
import fuzzm.poly.PolyBase;
import fuzzm.poly.PolyBool;
import fuzzm.poly.VariableID;
import fuzzm.value.hierarchy.EvaluatableValue;
import jkind.lustre.NamedType;
import jkind.lustre.Type;
import jkind.util.BigFraction;
import jkind.util.Util;

public class IntegerPoly extends PolyEvaluatableValue {

	AbstractPoly poly;
	
	public IntegerPoly(VariableID vid) {
		Map<VariableID,BigFraction> newCoefs = new HashMap<VariableID,BigFraction>();
		newCoefs.put(vid, BigFraction.ONE);
		poly = new PolyBase(newCoefs);
	}
	
	public IntegerPoly(AbstractPoly poly) {
		this.poly = poly;
	}
	
	@Override
	public EvaluatableValue cast(Type type) {
		if (type == NamedType.INT) return this;
		if (type == NamedType.REAL) {
			return new RationalPoly(poly);
		}
		throw new IllegalArgumentException();
	}

	@Override
	public EvaluatableValue int_divide(EvaluatableValue arg) {
		IntegerPoly right = (IntegerPoly) arg;
		if (! right.poly.isConstant()) throw new IllegalArgumentException();
		BigFraction Df = right.poly.getConstant();
		assert(Df.getDenominator().compareTo(BigInteger.ONE) == 0);
		BigInteger D = Df.getNumerator();
		assert(D.signum() != 0);
		AbstractPoly RWpoly = this.poly.rewrite(GlobalState.getRewrites());
		if (RWpoly.isConstant()) {
			BigFraction Nf = RWpoly.getConstant();
			assert(Nf.getDenominator().compareTo(BigInteger.ONE) == 0);
			BigInteger N = Nf.getNumerator();
			return new IntegerPoly(new PolyBase(new BigFraction(Util.smtDivide(N,D))));			
		}
		if (RWpoly.divisible(D)) {
			return new IntegerPoly(this.poly.div(D));
		}
		BigFraction cexF = RWpoly.evaluateCEX();
		assert(cexF.getDenominator().compareTo(BigInteger.ONE) == 0);
		BigInteger cex = cexF.getNumerator();
		BigInteger kcex = Util.smtDivide(cex,D);
		BigInteger mcex = cex.mod(D);
		VariableID least = RWpoly.trailingVariable();
		VariableID m = least.afterAlloc("m",NamedType.INT,new BigFraction(mcex));
		VariableID k = m.afterAlloc("k",NamedType.INT,new BigFraction(kcex));
		AbstractPoly ipoly = PolyBase.qpoly(D,k,m);
		AbstractPoly diff = RWpoly.subtract(ipoly);
		VariableID max = diff.leadingVariable();
		AbstractPoly rhs = diff.solveFor(max);
		PolyBool eq = PolyBool.equal0(diff);
		GlobalState.addRewrite(max,rhs);
		GlobalState.addConstraint(eq);
		AbstractPoly mp = new PolyBase(m);
		PolyBool gt0 = PolyBool.greater0(mp.negate()).not();
		PolyBool ltD = PolyBool.less0(mp.subtract(new BigFraction(D.abs())));
		GlobalState.addConstraint(gt0.and(ltD));
		return new IntegerPoly(new PolyBase(k));
	}
	
	@Override
	public EvaluatableValue modulus(EvaluatableValue arg) {
		IntegerPoly right = (IntegerPoly) arg;
		if (! right.poly.isConstant()) throw new IllegalArgumentException();
		BigFraction Df = right.poly.getConstant();
		assert(Df.getDenominator().compareTo(BigInteger.ONE) == 0);
		BigInteger D = Df.getNumerator();
		assert(D.signum() != 0);
		AbstractPoly RWpoly = this.poly.rewrite(GlobalState.getRewrites());
		if (RWpoly.isConstant()) {
			BigFraction Nf = RWpoly.getConstant();
			assert(Nf.getDenominator().compareTo(BigInteger.ONE) == 0);
			BigInteger N = Nf.getNumerator();
			return new IntegerPoly(new PolyBase(new BigFraction(N.mod(D))));			
		}
		if (RWpoly.divisible(D)) {
			return new IntegerPoly(new PolyBase(new BigFraction(RWpoly.getConstant().getNumerator().mod(D))));
		}
		BigFraction cexF = RWpoly.evaluateCEX();
		assert(cexF.getDenominator().compareTo(BigInteger.ONE) == 0);
		BigInteger cex = cexF.getNumerator();
		BigInteger kcex = Util.smtDivide(cex,D);
		BigInteger mcex = cex.mod(D);
		VariableID least = RWpoly.trailingVariable();
		VariableID m = least.afterAlloc("m",NamedType.INT,new BigFraction(mcex));
		VariableID k = m.afterAlloc("k",NamedType.INT,new BigFraction(kcex));
		AbstractPoly ipoly = PolyBase.qpoly(D,k,m);
		AbstractPoly diff = RWpoly.subtract(ipoly);
		VariableID max = diff.leadingVariable();
		AbstractPoly rhs = diff.solveFor(max);
		PolyBool eq = PolyBool.equal0(diff);
		GlobalState.addRewrite(max,rhs);
		GlobalState.addConstraint(eq);
		AbstractPoly mp = new PolyBase(m);
		PolyBool gt0 = PolyBool.greater0(mp.negate()).not();
		PolyBool ltD = PolyBool.less0(mp.subtract(new BigFraction(D.abs())));
		GlobalState.addConstraint(gt0.and(ltD));
		return new IntegerPoly(mp);
	}

	@Override
	public EvaluatableValue multiply(EvaluatableValue arg) {
		IntegerPoly right = (IntegerPoly) arg;
		IntegerPoly constant;
		if (this.poly.isConstant()) {
			constant = this;			
		} else {
			constant = right;
			right = this;
		}
		if (! constant.poly.isConstant()) throw new IllegalArgumentException();
		return new IntegerPoly(right.poly.multiply(constant.poly.getConstant()));
	}

	@Override
	public EvaluatableValue negate() {
		AbstractPoly res = this.poly.negate();
		PolyEvaluatableValue value = new IntegerPoly(res);
		//System.out.println(ID.location() + "(- " + this + ") evaluated to " + value + " [ " + value.cex() + "]");
		return value;
	}

	@Override
	public String toString() {
		return poly.toString();
	}

	@Override
	public EvaluatableValue plus(EvaluatableValue arg) {
		IntegerPoly right = (IntegerPoly) arg;
		PolyEvaluatableValue value = new IntegerPoly(this.poly.add(right.poly));
		//System.out.println(ID.location() + "(" + this + " + " + arg + ") evaluated to " + value + " [ " + value.cex() + "]");
		return value;
	}

	@Override
	public EvaluatableValue less(EvaluatableValue arg) {
		IntegerPoly right = (IntegerPoly) arg;
		return new BooleanPoly(PolyBool.less0(this.poly.subtract(right.poly)));
	}

	@Override
	public EvaluatableValue greater(EvaluatableValue arg) {
		IntegerPoly right = (IntegerPoly) arg;
		return new BooleanPoly(PolyBool.greater0(this.poly.subtract(right.poly)));
	}

	@Override
	public EvaluatableValue equalop(EvaluatableValue arg) {
		IntegerPoly right = (IntegerPoly) arg;
		return new BooleanPoly(PolyBool.equal0(this.poly.subtract(right.poly)));
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((poly == null) ? 0 : poly.hashCode());
		return result;
	}
	
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (! (obj instanceof IntegerPoly))
			return false;
		IntegerPoly other = (IntegerPoly) obj;
		return poly.equals(other.poly);
	}

	@Override
	public Type getType() {
		return NamedType.INT;
	}

	@Override
	public BigFraction cex() {
		return poly.evaluateCEX();
	}

	@Override
	public String toACL2() {
		return poly.toACL2();
	}

}
