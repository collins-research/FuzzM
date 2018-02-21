package jfuzz.heuristic;

import jfuzz.lustre.BooleanCtx;
import jfuzz.util.IntervalVector;
import jfuzz.util.JFuzzName;
import jfuzz.util.RatSignal;
import jkind.lustre.Expr;
import jkind.lustre.IdExpr;
import jkind.lustre.UnaryExpr;
import jkind.lustre.UnaryOp;

public class PropertyHeuristic implements HeuristicInterface {

	RatSignal lastCounterExample = new RatSignal();
	boolean ready = true;
	IntervalVector S;
	Expr prop;
	BooleanCtx bounds;
	
	public PropertyHeuristic(IntervalVector S, Expr prop) {
		this.prop = new UnaryExpr(UnaryOp.NOT,prop);
		this.S = S;
		this.bounds = new BooleanCtx();
	}
	
	@Override
	public boolean objective() {
		return false;
	}

	@Override
	public BooleanCtx hyp() {
		return bounds;
	}

	@Override
	public BooleanCtx constraint() {
		BooleanCtx res = new BooleanCtx(new IdExpr(JFuzzName.done));
		return res.implies(prop);
	}

	@Override
	public RatSignal target() {
		return RatSignal.uniformRandom(lastCounterExample.size(), S);
	}

	@Override
	public void wait(boolean objective) {
		ready = false;
	}

	@Override
	public boolean ready() {
		return ready;
	}

	@Override
	public void sat(boolean objective, RatSignal counterExample, BooleanCtx bounds) {
		lastCounterExample = counterExample;
		this.bounds = bounds;
		ready = true;
	}

	@Override
	public void unsat(boolean objective) {
		ready = true;
		bounds = new BooleanCtx();
	}

}
