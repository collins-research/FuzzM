/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.lustre.evaluation;

import java.util.ArrayList;

import fuzzm.value.hierarchy.EvaluatableValue;

public class EvaluatableArgList extends ArrayList<EvaluatableValue> {

	private static final long serialVersionUID = 7204007336721147321L;

	@Override
	public String toString() {
		String res = "(";
		String delimit = "";
		for (int index = 0; index<size(); index++) {
			res += delimit + get(index);
			delimit = ",";
		}
		return res + ")";
	}
	
}
