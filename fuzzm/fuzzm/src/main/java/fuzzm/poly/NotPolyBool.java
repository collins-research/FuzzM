/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.poly;

import fuzzm.lustre.evaluation.PolyFunctionMap;
import fuzzm.solver.SolverResults;
import fuzzm.util.RatSignal;

public class NotPolyBool extends PolyBool {

	protected NotPolyBool(boolean cex, VariableList body) {
		super(cex, body);
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
		String res = "(or\n";
		for (Variable vc: body) {
			res += vc.not().toACL2() + "\n";
		}
		return res + ")";
	}

	@Override
	protected boolean isNegated() {
		return true;
	}

	@Override
	public PolyBool not() {
		return new TruePolyBool(! cex,body);
	}

	@Override
	public boolean isFalse() {
		return (body.size() == 0);
	}

	@Override
	public boolean isTrue() {
		return false;
	}

	@Override
	public PolyBool normalize() {
		return this;
	}

	@Override
	public SolverResults optimize(SolverResults cex, PolyFunctionMap fmap, RatSignal target) {
		throw new IllegalArgumentException();
	}
	
}
