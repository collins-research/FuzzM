package jfuzz.value.hierarchy;

import jfuzz.value.instance.BooleanInterval;
import jkind.lustre.NamedType;
import jkind.lustre.Type;

public abstract class BooleanType extends InstanceType<BooleanType> implements BooleanTypeInterface, Joinable<BooleanType> {
	
	@Override
	abstract public EvaluatableValue ite(EvaluatableValue left, EvaluatableValue right);
	
	@Override
	abstract public EvaluatableType<BooleanType> not();
	
	@Override
	abstract public EvaluatableType<BooleanType> and(EvaluatableValue right);
	
	@Override
	abstract public EvaluatableType<BooleanType> or(EvaluatableValue right);
	
	@Override
	abstract public EvaluatableType<BooleanType> equalop(EvaluatableValue right);
	
	@Override
	abstract public BooleanType max(BooleanType right);
	
	@Override
	abstract public BooleanType min(BooleanType right);

	@Override
	public final Type getType() {
		return NamedType.BOOL;
	}
	
	@Override
	public final EvaluatableType<BooleanType> join(EvaluatableValue right) {
		@SuppressWarnings("unchecked")
		Joinable<BooleanType> rv = ((Joinable<BooleanType>) right);
		return rv.join2(this);
	}
	
	@Override
	public final EvaluatableType<BooleanType> join2(BooleanType left) {
		return min(left).newInterval(max(left));
	}
	
	@Override
	public final EvaluatableType<BooleanType> join2(IntervalType<BooleanType> left) {
		return left;
	}
	
	@Override
	public final EvaluatableType<BooleanType> newInterval(BooleanType max) {
		if (this.equals(max)) return this;
		return BooleanInterval.ARBITRARY;
	}	
	

}
