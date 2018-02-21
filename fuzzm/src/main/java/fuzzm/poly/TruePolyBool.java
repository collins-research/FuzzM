package jfuzz.poly;

import jfuzz.lustre.evaluation.PolyFunctionMap;
import jfuzz.solver.SolverResults;
import jfuzz.util.Debug;
import jfuzz.util.ProofWriter;
import jfuzz.util.RatSignal;

public class TruePolyBool extends PolyBool {

	protected TruePolyBool(boolean cex, VariableList body) {
		super(cex, body);
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
	protected boolean isNegated() {
		return false;
	}

	@Override
	public boolean isFalse() {
		return false;
	}

	@Override
	public boolean isTrue() {
		return (body.size() == 0);
	}

	@Override
	public PolyBool not() {
		if (body.size() == 1) {
			Variable c = body.peek();
			return new TruePolyBool(! cex, new VariableList(c.not()));
		}
		return new NotPolyBool(! cex,body);
	}

	@Override
	public PolyBool normalize() {
		VariableList x = body.normalize();
		PolyBool res = new TruePolyBool(cex,x);
		// It would sure be nice to generate proofs here that we could check ..
		if (Debug.isEnabled()) {
		    String s1 = this.toACL2();
		    String s2 = res.toACL2();
		    ProofWriter.printThms1("normalize", s1, s2);
		}
		return res;
	}

	@Override
	public SolverResults optimize(SolverResults cex, PolyFunctionMap fmap, RatSignal target) {
		//System.out.println(ID.location() + "Optimizing with :\n " + this);
		return body.optimize(cex,fmap,target);
	}

}
