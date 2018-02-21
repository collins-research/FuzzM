package jfuzz.solver;

import jfuzz.lustre.evaluation.FunctionLookupEV;
import jfuzz.util.RatSignal;

public class SolverResults {

	public RatSignal cex;
	public FunctionLookupEV fns;
	
	public SolverResults(RatSignal cex, FunctionLookupEV fns) {
		this.cex = cex;
		this.fns = fns;
	}

	@Override
	public String toString() {
		String res = "\n";
		res += fns.toString() + "\n";
		res += cex.toString() + "\n";
		return res;
	}
	
}
