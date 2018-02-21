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
import fuzzm.value.hierarchy.IntegerType;

public interface PolyValueInterface extends IntegerValueInterface {

	IntegerType int_divide2(PolyValue left);
	IntegerType modulus2(PolyValue left);
	IntegerType max2(PolyValue left);
	IntegerType min2(PolyValue left);
	IntegerType multiply2(PolyValue left);
	IntegerType plus2(PolyValue left);
	BooleanType less2(PolyValue left);
	BooleanType greater2(PolyValue left);
	BooleanType equalop2(PolyValue left);
}
