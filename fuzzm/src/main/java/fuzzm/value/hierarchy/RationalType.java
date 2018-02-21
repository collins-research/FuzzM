package jfuzz.value.hierarchy;

import jkind.lustre.NamedType;
import jkind.lustre.Type;

public abstract class RationalType extends NumericType<RationalType> implements RationalTypeInterface {
	
	@Override
	public final EvaluatableType<RationalType> divide(EvaluatableValue right) {
		RationalTypeInterface rv = (RationalTypeInterface) right;
		return rv.divide2(this);
	}

	@Override
	public final EvaluatableType<RationalType> divide2(RationalType left) {
		return this.divide(left);
	}

	@Override
	public final EvaluatableType<RationalType> divide2(RationalIntervalType left) {
		RationalType min = left.getLow();
		RationalType max = left.getHigh();
		RationalType q1 = min.divide(this);
		RationalType q2 = max.divide(this);
		return q1.min(q2).newInterval(q1.max(q2));
	}

	abstract public RationalType divide(RationalType right);
	
	@Override
	public final Type getType() {
		return NamedType.REAL;
	}
	
}
