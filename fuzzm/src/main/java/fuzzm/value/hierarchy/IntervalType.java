package jfuzz.value.hierarchy;

public abstract class IntervalType<T extends InstanceType<T>> extends EvaluatableType<T> implements Joinable<T> {

	@Override
	abstract public T getLow();
	@Override
	abstract public T getHigh();

	abstract public EvaluatableType<T> newInterval(InstanceType<T> min, InstanceType<T> max);

	@Override
	public final EvaluatableType<T> join(EvaluatableValue right) {
		@SuppressWarnings("unchecked")
		Joinable<T> rv = ((Joinable<T>) right);
		return rv.join2(this);
	}

	@Override
	public final EvaluatableType<T> join2(IntervalType<T> left) {
		return newInterval(getLow().min(left.getLow()),getHigh().max(left.getHigh()));
	}

	@Override
	public final EvaluatableType<T> join2(T left) {
		return newInterval(getLow().min(left),getHigh().max(left));
	}
	
	// Perhaps these should be only in the instance hierarchy?
	@Override
	public final EvaluatableType<IntegerType> integerType() {
		return ((InstanceType<IntegerType>) getLow().integerType()).newInterval((IntegerType) getHigh().integerType());
	}

	@Override
	public final EvaluatableType<BooleanType> booleanType() {
		return ((InstanceType<BooleanType>) getLow().booleanType()).newInterval((BooleanType) getHigh().booleanType());
	}
	
	@Override
	public final EvaluatableType<RationalType> rationalType() {
		return ((InstanceType<RationalType>) getLow().rationalType()).newInterval((RationalType) getHigh().rationalType());
	}
	
	@Override
	public final int signum() {
		int lowsig = getLow().signum();
		int highsig = getHigh().signum();
		if ((lowsig > 0) && (highsig > 0)) return +1;
		if ((lowsig < 0) && (highsig < 0)) return -1;
		return 0;
	}
	
}
