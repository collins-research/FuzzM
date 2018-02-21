package jfuzz.value.poly;

import java.math.BigInteger;
import java.util.HashMap;
import java.util.Map;

import jfuzz.poly.AbstractPoly;
import jfuzz.poly.PolyBase;
import jfuzz.poly.PolyBool;
import jfuzz.poly.VariableID;
import jfuzz.value.hierarchy.EvaluatableValue;
import jkind.lustre.NamedType;
import jkind.lustre.Type;
import jkind.util.BigFraction;

public class RationalPoly extends PolyEvaluatableValue {

	AbstractPoly poly;
	
	public RationalPoly(VariableID vid) {
		Map<VariableID,BigFraction> newCoefs = new HashMap<VariableID,BigFraction>();
		newCoefs.put(vid, BigFraction.ONE);
		poly = new PolyBase(newCoefs);
	}
	
	public RationalPoly(AbstractPoly poly) {
		this.poly = poly;
	}
	
	@Override
	public EvaluatableValue cast(Type type) {
		if (type == NamedType.REAL) return this;
		if (type == NamedType.INT) {
			AbstractPoly RWpoly = this.poly.rewrite(GlobalState.getRewrites());
			BigInteger D = BigInteger.ONE;
			if (RWpoly.isConstant()) {
				BigFraction Nf = RWpoly.getConstant();
				return new IntegerPoly(new PolyBase(new BigFraction(Nf.floor())));			
			}
			if (RWpoly.divisible(D)) {
				return new IntegerPoly(this.poly.div(D));
			}
			BigFraction cexF = RWpoly.evaluateCEX();
			BigFraction kcex = new BigFraction(cexF.floor());
			BigFraction mcex = cexF.subtract(kcex);
			VariableID least = RWpoly.trailingVariable();
			VariableID m = least.afterAlloc("m",NamedType.REAL,mcex);
			VariableID k = m.afterAlloc("k",NamedType.INT,kcex);
			AbstractPoly qpoly = PolyBase.qpoly(D,k,m);
			AbstractPoly diff = RWpoly.subtract(qpoly);
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
		throw new IllegalArgumentException();
	}

	@Override
	public EvaluatableValue multiply(EvaluatableValue arg) {
		RationalPoly right = (RationalPoly) arg;
		RationalPoly constant;
		if (this.poly.isConstant()) {
			constant = this;			
		} else {
			constant = right;
			right = this;
		}
		if (! constant.poly.isConstant()) throw new IllegalArgumentException();
		return new RationalPoly(right.poly.multiply(constant.poly.getConstant()));
	}

	@Override
	public EvaluatableValue negate() {
		AbstractPoly res = this.poly.negate();
		return new RationalPoly(res);
	}

	@Override
	public String toString() {
		return poly.toString();
	}

	@Override
	public EvaluatableValue plus(EvaluatableValue arg) {
		RationalPoly right = (RationalPoly) arg;
		return new RationalPoly(this.poly.add(right.poly));
	}

	@Override
	public EvaluatableValue less(EvaluatableValue arg) {
		RationalPoly right = (RationalPoly) arg;
		return new BooleanPoly(PolyBool.less0(this.poly.subtract(right.poly)));
	}

	@Override
	public EvaluatableValue greater(EvaluatableValue arg) {
		RationalPoly right = (RationalPoly) arg;
		return new BooleanPoly(PolyBool.greater0(this.poly.subtract(right.poly)));
	}

	@Override
	public EvaluatableValue equalop(EvaluatableValue arg) {
		RationalPoly right = (RationalPoly) arg;
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
		if (! (obj instanceof RationalPoly))
			return false;
		RationalPoly other = (RationalPoly) obj;
		return poly.equals(other.poly);
	}

	@Override
	public Type getType() {
		return NamedType.REAL;
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
