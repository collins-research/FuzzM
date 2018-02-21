/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.value.hierarchy;

import fuzzm.util.Debug;
import fuzzm.util.ID;

abstract public class NumericIntervalType<T extends NumericType<T>> extends IntervalType<T> implements NumericTypeInterface<T> {
	
	@Override
	public final EvaluatableType<T> multiply(EvaluatableValue right) {
		@SuppressWarnings("unchecked")
		NumericTypeInterface<T> rv = ((NumericTypeInterface<T>) right);
		return rv.multiply2(this);
	}
	
	@Override
	public final EvaluatableType<T> multiply2(NumericIntervalType<T> left) {
		T max1 = getHigh();
		T max2 = left.getHigh();
		T min1 = getLow();
		T min2 = left.getLow();
		T maxmin = max1.multiply2(min2);
		T maxmax = max1.multiply(max2);
		T minmin = min1.multiply(min2);
		T minmax = min1.multiply(max2);
		return newInterval(maxmin.min(maxmax,minmin,minmax),maxmin.max(maxmax,minmin,minmax));
	}
	
	@Override
	public final EvaluatableType<T> multiply2(NumericType<T> left) {
		T max1 = getHigh();
		T min1 = getLow();
		T p1 = max1.multiply(left);
		T p2 = min1.multiply(left);
		return newInterval(p1.min(p2),p1.max(p2));
	}
	
	@Override
	public final EvaluatableType<T> plus(EvaluatableValue right) {
		@SuppressWarnings("unchecked")
		NumericTypeInterface<T> rv = ((NumericTypeInterface<T>) right);
		return rv.plus2(this);
	}
	
	@Override
	public final EvaluatableType<T> plus2(NumericIntervalType<T> left) {
		T min = left.getLow().plus(getLow());
		T max = left.getHigh().plus(getHigh());
		return newInterval(min,max);
	}
	
	@Override
	public final EvaluatableType<T> plus2(NumericType<T> left) {
		T min = left.plus(getLow());
		T max = left.plus(getHigh());
		return newInterval(min,max);
	}
	
	@Override
	public final EvaluatableType<BooleanType> less(EvaluatableValue right) {
		@SuppressWarnings("unchecked")
		NumericTypeInterface<T> rv = ((NumericTypeInterface<T>) right);
		return rv.less2(this);
	}

	@Override
	public final EvaluatableType<BooleanType> less2(NumericIntervalType<T> left) {
		// this assumes that min != max
		if (getLow().greater(left.getHigh()).isTrue()) return newBooleanType(true);
		if (left.getLow().less(getHigh()).isFalse()) return newBooleanType(false);
		return newBooleanInterval();
	}
	
	@Override
	public final EvaluatableType<BooleanType> less2(NumericType<T> left) {
		// this assumes that min != max
		if (getLow().greater(left).isTrue()) return newBooleanType(true);
		if (left.less(getHigh()).isFalse()) return newBooleanType(false);
		return newBooleanInterval();
	}
	
	@Override
	public final EvaluatableType<BooleanType> greater(EvaluatableValue right) {
		@SuppressWarnings("unchecked")
		NumericTypeInterface<T> rv = ((NumericTypeInterface<T>) right);
		return rv.greater2(this);
	}
	
	@Override
	public final EvaluatableType<BooleanType> greater2(NumericIntervalType<T> left) {
		// this assumes that min != max
		if (left.getLow().greater(getHigh()).isTrue()) return newBooleanType(true);
		if (getLow().less(left.getHigh()).isFalse())   return newBooleanType(false);
		return newBooleanInterval();
	}
	
	@Override
	public final EvaluatableType<BooleanType> greater2(NumericType<T> left) {
		// this assumes that min != max
		if (left.greater(getHigh()).isTrue()) return newBooleanType(true);
		if ((getLow().less(left)).isFalse())  return newBooleanType(false);
		return newBooleanInterval();
	}
	
	@Override
	public final EvaluatableType<BooleanType> equalop(EvaluatableValue right) {
		@SuppressWarnings("unchecked")
		NumericTypeInterface<T> rv = ((NumericTypeInterface<T>) right);
		return rv.equalop2(this);
	}
	
	@Override
	public final EvaluatableType<BooleanType> equalop2(NumericIntervalType<T> left) {
		// TODO: we should probably keep this in the Value domain. (ie: do not use isTrue())
		EvaluatableType<BooleanType> res;
		if (left.getHigh().less(getLow()).isTrue() || getHigh().less(left.getLow()).isTrue()) {
			if (Debug.isEnabled()) System.err.println(ID.location() + "(" + left.getHigh() + " < " + getLow() + " || " + getHigh() + " < " + left.getLow() + ")");
			res = newBooleanType(false);
		} else {
			res = newBooleanInterval();
		}
		if (Debug.isEnabled()) System.err.println(ID.location() + "(" + left + " == " + this + ") = " + res);
		return res;
	}
	
	@Override
	public final EvaluatableType<BooleanType> equalop2(NumericType<T> left) {
		// this assumes that min != max
		EvaluatableType<BooleanType> res;
		if (left.less(getLow()).isTrue() || left.greater(getHigh()).isTrue()) {
			if (Debug.isEnabled()) System.err.println(ID.location() + "(" + left + " < " + getLow() + " || " + getHigh() + " < " + left + ")");
			res = newBooleanType(false);
		} else {
			res = newBooleanInterval();
		}
		if (Debug.isEnabled()) System.err.println(ID.location() + "(" + left + " == " + this + ") = " + res);
		return res;
	}
	
	@Override
	public final EvaluatableType<T> negate() {
		return newInterval(getHigh().negate(),getLow().negate());
	}
	
}
