package jfuzz.poly;

import jfuzz.lustre.evaluation.PolyFunctionMap;
import jfuzz.solver.SolverResults;
import jfuzz.util.RatSignal;

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
