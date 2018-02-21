/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.value.hierarchy;

import java.math.BigInteger;

import fuzzm.util.Debug;
import fuzzm.util.ID;

public abstract class NumericType<T extends NumericType<T>> extends InstanceType<T> implements NumericTypeInterface<T>,Joinable<T> {

	@Override
	public final EvaluatableType<T> join(EvaluatableValue right) {
		@SuppressWarnings("unchecked")
		Joinable<T> rv = ((Joinable<T>) right);
		@SuppressWarnings("unchecked")
		T left = ((T) this);
		return rv.join2(left);
	}
	
	@Override
	public final EvaluatableType<T> join2(T left) {
		return min(left).newInterval(max(left));
	}
	
	@Override
	public final EvaluatableType<T> join2(IntervalType<T> left) {
		return min(left.getLow()).newInterval(max(left.getHigh()));
	}
	
	@Override
	abstract public EvaluatableType<T> newInterval(T max);
	
	@Override
	public final EvaluatableType<T> multiply(EvaluatableValue right) {
		@SuppressWarnings("unchecked")
		NumericTypeInterface<T> rv = ((NumericTypeInterface <T>) right);
		return rv.multiply2(this);
	}
	
	@Override
	public final EvaluatableType<T> multiply2(NumericIntervalType<T> left) {
		T max2 = left.getHigh();
		T min2 = left.getLow();
		T p1 = multiply(min2);
		T p2 = multiply(max2);
		return p1.min(p2).newInterval(p1.max(p2));
	}
		
	@Override
	public final T multiply2(NumericType<T> left) {
		return left.multiply(this);
	}
		
	abstract public T multiply(NumericType<T> right);
	
	@Override
	public final EvaluatableType<T> plus(EvaluatableValue right) {
		@SuppressWarnings("unchecked")
		NumericTypeInterface<T> rv = ((NumericTypeInterface<T>) right);
		return rv.plus2(this);
	}
	
	@Override
	public final EvaluatableType<T> plus2(NumericIntervalType<T> left) {
		@SuppressWarnings("unchecked")
		T right = ((T) this);
		T min = left.getLow().plus(right);
		T max = left.getHigh().plus(right);
		return min.newInterval(max);
	}
	
	@Override
	public final NumericType<T> plus2(NumericType<T> left) {
		@SuppressWarnings("unchecked")
		T right = ((T) this);
		return left.plus(right);
	}

	abstract public T plus(NumericType<T> right);
	
	@Override
	public final EvaluatableType<BooleanType> less(EvaluatableValue right) {
		@SuppressWarnings("unchecked")
		NumericTypeInterface<T> rv = ((NumericTypeInterface<T>) right);
		return rv.less2(this);
	};

	@Override
	public final EvaluatableType<BooleanType> less2(NumericIntervalType<T> left) {
		// this assumes that min != max
		if (this.greater(left.getHigh()).isTrue()) return newBooleanType(true);
		if (left.getLow().less(this).isFalse())  return newBooleanType(false);
		//System.out.println(ID.location() + "*** " + "("+ left + " < " + this + ") = [F,T}");
		return newBooleanInterval();
	}
	
	@Override
	public final EvaluatableType<BooleanType> less2(NumericType<T> left) {
		return left.less(this);
	}
	
	abstract public BooleanType less(NumericType<T> right);
	
	@Override
	public final EvaluatableType<BooleanType> greater(EvaluatableValue right) {
		@SuppressWarnings("unchecked")
		NumericTypeInterface<T> rv = ((NumericTypeInterface<T>) right);
		return rv.greater2(this);
	}
	
	@Override
	public final EvaluatableType<BooleanType> greater2(NumericIntervalType<T> left) {
		// this assumes that min != max
		if (left.getLow().greater(this).isTrue())  return newBooleanType(true);
		if (this.less(left.getHigh()).isFalse()) return newBooleanType(false);
		return newBooleanInterval();
	}
	
	@Override
	public final EvaluatableType<BooleanType> greater2(NumericType<T> left) {
		return left.greater(this);
	}
	
	abstract public BooleanType greater(NumericType<T> right);
	
	@Override
	public final EvaluatableType<BooleanType> equalop(EvaluatableValue right) {
		@SuppressWarnings("unchecked")
		NumericTypeInterface<T> rv = ((NumericTypeInterface<T>) right);
		return rv.equalop2(this);
	}
	
	@Override
	public final EvaluatableType<BooleanType> equalop2(NumericIntervalType<T> left) {
		// this assumes that min != max
		EvaluatableType<BooleanType> res;
		if (this.less(left.getLow()).isTrue() || this.greater(left.getHigh()).isTrue()) {
			if (Debug.isEnabled()) System.err.println(ID.location() + "(" + this + " < " + left.getLow() + " || " + left.getHigh() + " < " + this + ")");
			res = newBooleanType(false);
		} else {
			res = newBooleanInterval();
		}
		if (Debug.isEnabled()) System.err.println(ID.location() + "(" + left + " == " + this + ") = " + res);
		return res;
	}
	
	@Override
	public final EvaluatableType<BooleanType> equalop2(NumericType<T> left) {
		return left.equalop(this);
	}
	
	abstract public BooleanType equalop(NumericType<T> right);
	
	@Override
	abstract public T negate();
	
	abstract public T abs();
	
	abstract public T valueOf(BigInteger arg);
	
}
