/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.value.hierarchy;

public interface NumericTypeInterface<T extends NumericType<T>> {
	
	EvaluatableType<T> multiply(EvaluatableValue right);
	EvaluatableType<T> multiply2(NumericType<T> left);
	EvaluatableType<T> multiply2(NumericIntervalType<T> left);
	
	EvaluatableType<T> plus(EvaluatableValue right);
	EvaluatableType<T> plus2(NumericType<T> left);
	EvaluatableType<T> plus2(NumericIntervalType<T> left);
	
	EvaluatableType<BooleanType> less(EvaluatableValue right);
	EvaluatableType<BooleanType> less2(NumericType<T> left);
	EvaluatableType<BooleanType> less2(NumericIntervalType<T> left);
	
	EvaluatableType<BooleanType> greater(EvaluatableValue right);
	EvaluatableType<BooleanType> greater2(NumericType<T> left);
	EvaluatableType<BooleanType> greater2(NumericIntervalType<T> left);
	
	EvaluatableType<BooleanType> equalop(EvaluatableValue right);
	EvaluatableType<BooleanType> equalop2(NumericType<T> left);
	EvaluatableType<BooleanType> equalop2(NumericIntervalType<T> left);
	
}
