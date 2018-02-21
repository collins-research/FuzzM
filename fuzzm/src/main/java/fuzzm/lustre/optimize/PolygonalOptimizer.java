package jfuzz.lustre.optimize;

import jfuzz.lustre.generalize.PolyGeneralizationResult;
import jfuzz.lustre.generalize.PolygonalGeneralizer;
import jfuzz.solver.SolverResults;
import jfuzz.util.EvaluatableSignal;
import jfuzz.util.RatSignal;
import jkind.lustre.Program;

public class PolygonalOptimizer {

	public static SolverResults optimize(SolverResults sln, RatSignal target, String property, Program main) {
		//System.out.println(ID.location() + sln);
		EvaluatableSignal cex = sln.cex.evaluatableSignal();
		
		//Debug.setLogic(true);

		PolyGeneralizationResult res = PolygonalGeneralizer.generalizeInterface(cex, property, sln.fns, main);
		//System.out.println(ID.location() + "poly = " + res.result);
		SolverResults opsln = res.result.optimize(sln,res.fmap,target);
		//System.out.println(ID.location() + opsln);
		return opsln;
	}
	
}
