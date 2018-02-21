/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.lustre.generalize;

import fuzzm.lustre.evaluation.PolyFunctionMap;
import fuzzm.poly.PolyBool;

public class PolyGeneralizationResult {
	public PolyBool result;
	public PolyFunctionMap fmap;
	public PolyGeneralizationResult(PolyBool res, PolyFunctionMap fmap) {
		this.result = res;
		this.fmap = fmap;
	}
}
