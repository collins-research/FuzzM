/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.value.hierarchy;

public interface RationalTypeInterface {
	
	public EvaluatableType<RationalType> divide(EvaluatableValue right);
	public EvaluatableType<RationalType> divide2(RationalType left);
	public EvaluatableType<RationalType> divide2(RationalIntervalType left);

}
