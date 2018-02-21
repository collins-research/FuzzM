/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.value.instance;

import fuzzm.value.hierarchy.BooleanType;
import fuzzm.value.hierarchy.EvaluatableType;
import fuzzm.value.hierarchy.IntegerType;
import fuzzm.value.hierarchy.NumericType;

public interface IntegerValueInterface /*extends NumericTypeInterface<IntegerType>*/ {
	
	IntegerType int_divide(IntegerType right);
	IntegerType int_divide2(IntegerValue left);
	IntegerType int_divide2(IntegerInfinity left);
	
	EvaluatableType<IntegerType> modulus(IntegerType right);
	IntegerType modulus2(IntegerValue left);
	EvaluatableType<IntegerType> modulus2(IntegerInfinity left);
	
	IntegerType max(IntegerType right);
	IntegerType max2(IntegerValue left);
	IntegerType max2(IntegerInfinity left);

	IntegerType min(IntegerType right);
	IntegerType min2(IntegerValue left);
	IntegerType min2(IntegerInfinity left);

	IntegerType multiply(NumericType<IntegerType> right);
	IntegerType multiply2(IntegerValue left);
	IntegerType multiply2(IntegerInfinity left);
	
	IntegerType plus(NumericType<IntegerType> right);
	IntegerType plus2(IntegerValue left);
	IntegerType plus2(IntegerInfinity left);
	
	BooleanType less(NumericType<IntegerType> right);
	BooleanType less2(IntegerValue left);
	BooleanType less2(IntegerInfinity left);
	
	BooleanType greater(NumericType<IntegerType> right);
	BooleanType greater2(IntegerValue left);
	BooleanType greater2(IntegerInfinity left);
	
	BooleanType equalop(NumericType<IntegerType> right);
	BooleanType equalop2(IntegerValue left);
	BooleanType equalop2(IntegerInfinity left);

}
