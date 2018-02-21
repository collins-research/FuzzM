package jfuzz.heuristic;

import jfuzz.lustre.BooleanCtx;
import jfuzz.util.RatSignal;

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
