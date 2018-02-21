/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.lustre.optimize;

import fuzzm.lustre.generalize.PolyGeneralizationResult;
import fuzzm.lustre.generalize.PolygonalGeneralizer;
import fuzzm.solver.SolverResults;
import fuzzm.util.Debug;
import fuzzm.util.EvaluatableSignal;
import fuzzm.util.ID;
import fuzzm.util.ProofWriter;
import fuzzm.util.RatSignal;
import jkind.lustre.Program;

public class PolygonalOptimizer {

	public static SolverResults optimize(SolverResults sln, RatSignal target, String name, String property, Program main) {
		//System.out.println(ID.location() + sln);
		EvaluatableSignal cex = sln.cex.evaluatableSignal();
		
		PolyGeneralizationResult res = PolygonalGeneralizer.generalizeInterface(cex, name, property, sln.fns, main);
		// System.err.println(ID.location() + "Solution poly      = " + res.result);
		SolverResults opsln = res.result.optimize(sln,res.fmap,target);
		if (Debug.proof()) {
		    ProofWriter.printEval(ID.location(), "optEval_" + name, res.result.toACL2(), opsln.cex.toACL2());
		}		
		return opsln;
	}
	
}
