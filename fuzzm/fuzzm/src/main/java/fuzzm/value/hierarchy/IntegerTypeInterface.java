/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.value.hierarchy;

public interface IntegerTypeInterface {
	
	public EvaluatableType<IntegerType> int_divide(EvaluatableValue right);
	public EvaluatableType<IntegerType> int_divide2(IntegerType left);
	public EvaluatableType<IntegerType> int_divide2(IntegerIntervalType left);

	public EvaluatableType<IntegerType> modulus(EvaluatableValue right);
	public EvaluatableType<IntegerType> modulus2(IntegerType left);
	public EvaluatableType<IntegerType> modulus2(IntegerIntervalType left);

}
