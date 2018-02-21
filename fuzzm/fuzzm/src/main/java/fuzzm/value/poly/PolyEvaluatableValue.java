/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.value.poly;

import fuzzm.value.hierarchy.EvaluatableValue;
import jkind.util.BigFraction;

public abstract class PolyEvaluatableValue extends EvaluatableValue implements Comparable<PolyEvaluatableValue> {

	public abstract BigFraction cex();
	
	@Override
	public int compareTo(PolyEvaluatableValue o) {
		return cex().compareTo(o.cex());
	}

	public abstract String toACL2();

}
