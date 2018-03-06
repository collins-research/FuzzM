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
import fuzzm.util.RatSignal;

public class FalsePolyBool extends PolyBool {

	protected FalsePolyBool(boolean cex, VariableList body) {
		super(cex, body);
	    assert(! cex);
	}
	
	protected FalsePolyBool(Variable var) {
        this(! var.cex, new VariableList(var));
    }

    @Override
	public String toString() {
		String res = "(not (\n ";
		String delimit = "";
		for (Variable vc: body) {
			res += delimit + vc;
			delimit = " &\n ";
		}
		return res + "\n))";
	}

	@Override
	public String toACL2() {
		String res = "(not (and\n";
		for (Variable vc: body) {
			res += vc.toACL2() + "\n";
		}
		return res + "))";
	}

	@Override
	public boolean isNegated() {
		return true;
	}

	@Override
	public PolyBool not() {
		return new TruePolyBool(! cex,body);
	}

	@Override
	public boolean isAlwaysFalse() {
		return (body.size() == 0);
	}

	@Override
	public boolean isAlwaysTrue() {
		return false;
	}

	@Override
	public PolyBool normalize() {
		return this;
	}

	@Override
	public SolverResults optimize(SolverResults cex, PolyFunctionMap fmap, RatSignal target) {
		return cex;
	}

    @Override
    public List<Variable> getArtifacts() {
        throw new IllegalArgumentException();
    }

    @Override
    public List<Variable> getTargets() {
        throw new IllegalArgumentException();
    }
	
}
