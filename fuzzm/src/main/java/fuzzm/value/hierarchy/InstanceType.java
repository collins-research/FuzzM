package jfuzz.value.hierarchy;

import jkind.util.BigFraction;

abstract public class InstanceType<T extends InstanceType<T>> extends EvaluatableType<T> {

	abstract public T max(T base);	
	@SafeVarargs
	public final T max(T other, T ... rest) {
		T res = max(other);
		for (T next: rest) {
			res = res.max(next);
		}
		return res;
	}
	
	abstract public T min(T base);
	@SafeVarargs
	public final T min(T other, T ... rest) {
		T res = min(other);
		for (T next: rest) {
			res = res.min(next);
		}
		return res;
	}
	
	abstract public EvaluatableType<T> newInterval(T max);
	
	@Override
	public final T getLow() {
		@SuppressWarnings("unchecked")
		T value = ((T) this);
		return value;
	}
	
	@Override
	public final T getHigh() {
		@SuppressWarnings("unchecked")
		T value = ((T) this);
		return value;
	}
	
	abstract public boolean isFinite();

	abstract public BigFraction getValue();
	
}
