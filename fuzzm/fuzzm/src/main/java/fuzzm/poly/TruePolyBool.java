/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.poly;

import java.util.List;

import fuzzm.lustre.evaluation.PolyFunctionMap;
import fuzzm.solver.SolverResults;
import fuzzm.util.Debug;
import fuzzm.util.ID;
import fuzzm.util.ProofWriter;
import fuzzm.util.RatSignal;

public class TruePolyBool extends PolyBool {

	protected TruePolyBool(boolean cex, VariableList body) {
		super(cex, body);
	    assert(cex);
	}

	@Override
	public String toString() {
		String res = "(\n ";
		String delimit = "";
		for (Variable vc: body) {
			res += delimit + vc;
			delimit = " &&\n ";
		}
		return res + "\n)";
	}

	@Override
	public String toACL2() {
		String res = "(and\n";
		for (Variable vc: body) {
			res += vc.toACL2() + "\n";
		}
		return res + "\n)";
	}

	public TruePolyBool(Variable c) {
		super(c);
	}

	@Override
	public boolean isNegated() {
		return false;
	}

	@Override
	public boolean isAlwaysFalse() {
		return false;
	}

	@Override
	public boolean isAlwaysTrue() {
		return (body.size() == 0);
	}

	@Override
	public PolyBool not() {
		return new FalsePolyBool(! cex,body);
	}

	@Override
	public PolyBool normalize() {
		VariableList x = body.normalize();
		PolyBool res = new TruePolyBool(cex,x);
		// It would sure be nice to generate proofs here that we could check ..
		if (Debug.isEnabled()) {
		    String s1 = this.toACL2();
		    String s2 = res.toACL2();
		    ProofWriter.printRefinement(ID.location(),"normalize", s1, s2);
		}
		return res;
	}

	@Override
	public SolverResults optimize(SolverResults cex, PolyFunctionMap fmap, RatSignal target) {
		//System.out.println(ID.location() + "Optimizing with :\n " + this);
		return body.optimize(cex,fmap,target);
	}

    @Override
    public List<Variable> getArtifacts() {
        return body.getArtifacts();
    }

    @Override
    public List<Variable> getTargets() {
        return body.getTargets();
    }

}
