/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.solver;

import fuzzm.lustre.evaluation.FunctionLookupEV;
import fuzzm.util.RatSignal;

public class SolverResults {

	public RatSignal cex;
	public FunctionLookupEV fns;
	public long time;
	
	public SolverResults(long time, RatSignal cex, FunctionLookupEV fns) {
		this.cex = cex;
		this.fns = fns;
		this.time = time;
	}

	@Override
	public String toString() {
		String res = "\n";
		res += fns.toString() + "\n";
		res += cex.toString() + "\n";
		return res;
	}
	
}
