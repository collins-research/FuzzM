/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.value.hierarchy;

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
