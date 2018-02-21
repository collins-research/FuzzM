/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.heuristic;

import fuzzm.lustre.BooleanCtx;
import fuzzm.util.RatSignal;

public interface HeuristicInterface {

	boolean objective();

	BooleanCtx hyp();

	BooleanCtx constraint();

	RatSignal target();

	// Mark this feature as "in process"
	void wait(boolean objective);

	// Query the status of this feature
	boolean ready();

	// Resolve the feature as SAT
	void sat(boolean objective, RatSignal counterExample, BooleanCtx bounds);

	// Resolve the feature as UNSAT
	void unsat(boolean objective);

}
