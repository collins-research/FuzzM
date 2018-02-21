/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.value.hierarchy;

public interface Joinable<T extends InstanceType<T>> {
	public EvaluatableType<T> join(EvaluatableValue right);
	public EvaluatableType<T> join2(IntervalType<T> left);
	public EvaluatableType<T> join2(T left);
}
