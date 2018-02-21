package jfuzz.value.poly;

import jfuzz.poly.PolyBool;
import jfuzz.poly.TruePolyBool;
import jfuzz.poly.VariableBoolean;
import jfuzz.poly.VariableID;
import jfuzz.value.hierarchy.EvaluatableValue;
import jkind.lustre.NamedType;
import jkind.lustre.Type;
import jkind.lustre.values.Value;
import jkind.util.BigFraction;

public class BooleanPoly extends PolyEvaluatableValue {

	public final static BooleanPoly TRUE  = new BooleanPoly(PolyBool.TRUE);
	public final static BooleanPoly FALSE = new BooleanPoly(PolyBool.FALSE);
	
	public PolyBool value;
	
	public BooleanPoly(PolyBool value) {
		this.value = value;
	}
	
	public BooleanPoly(VariableID value) {
		this.value = new TruePolyBool(new VariableBoolean(value));
	}
	
	// not()
	
	@Override
	public EvaluatableValue not() {
		return new BooleanPoly(value.not());
	}
	
	@Override
	public EvaluatableValue and(EvaluatableValue arg) {
		BooleanPoly right = (BooleanPoly) arg;		
		return new BooleanPoly(value.and(right.value));
	}

	@Override
	public EvaluatableValue or(EvaluatableValue arg) {
		BooleanPoly right = (BooleanPoly) arg;
		return new BooleanPoly(value.or(right.value));
	}

	@Override
	public EvaluatableValue equalop(EvaluatableValue arg) {
		BooleanPoly right = (BooleanPoly) arg;
		return new BooleanPoly(value.iff(right.value));
	}


	public boolean isTrue() {
		return value.isTrue();
	}

	public boolean isFalse() {
		return value.isFalse();
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (!( obj instanceof BooleanPoly))
			return false;
		BooleanPoly other = (BooleanPoly) obj;
		return value.equals(other.value);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + value.hashCode();
		return result;
	}

	@Override
	public String toString() {
		return value.toString();
	}

	@Override
	public EvaluatableValue cast(Type type) {
		if (type == NamedType.BOOL) return this;
		throw new IllegalArgumentException();
	}

	@Override
	public Type getType() {
		return NamedType.BOOL;
	}

	public Value ite(EvaluatableValue thenValue, EvaluatableValue elseValue) {
		BooleanPoly thenArg = (BooleanPoly) thenValue;
		BooleanPoly elseArg = (BooleanPoly) elseValue;
		PolyBool p1 = value.and(thenArg.value);
		PolyBool p2 = value.not().and(elseArg.value);
		return new BooleanPoly(p1.or(p2));
	}

	@Override
	public BigFraction cex() {
		return (value.cex) ? BigFraction.ONE : BigFraction.ZERO;
	}

	@Override
	public String toACL2() {
		return value.toACL2();
	}

}
