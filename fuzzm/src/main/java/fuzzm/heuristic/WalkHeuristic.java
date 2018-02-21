package jfuzz.heuristic;

import java.util.ArrayList;
import java.util.List;

import jfuzz.lustre.BooleanCtx;
import jfuzz.util.IntervalVector;
import jfuzz.util.RatSignal;
import jkind.lustre.Expr;

/***
 * 
 * The Walk heuristic attempts to induce a kind of
 * random walk through the state space.
 * 
 * TODO: We should consider Astroid space: items
 * beyond a given axis boundary wrap back to the other
 * side of the state space.  To do this we need well
 * established bounds.  You could probably test this
 * theory with the current setup.  Would probably
 * require changes to optimization ..
 *
 */
public class WalkHeuristic extends FuzzHeuristic {

	RatSignal sat[] = new RatSignal[2];
	RatSignal target[] = new RatSignal[2];
	List<RatSignal> pivot[];
	BooleanCtx[] cube = { new BooleanCtx(), new BooleanCtx() };
	// String inputs[];
	IntervalVector S;
	
	@SuppressWarnings("unchecked")
	public WalkHeuristic(IntervalVector S, int id, Expr prop)  {
		super(id,prop);
		pivot = (List<RatSignal>[]) new ArrayList[2];
		pivot[0] = new ArrayList<RatSignal>();
		pivot[1] = new ArrayList<RatSignal>();
		//this.inputs = inputs;
		this.S = S;
		//List<String> x = D.stream().map(z -> z.name).collect(Collectors.toList());
		target[0] = new RatSignal(); // RatSignal.random(1,S);
		target[1] = new RatSignal(); // RatSignal.random(1,S);
		sat[0]    = new RatSignal();
		sat[1]    = new RatSignal();
	}
	
	private void rotateTarget(boolean objective) {
		int index = index(objective);
		target[index] = sat[index(! objective)];
		pivot[index].clear();
	}
	
	@Override
	public void sat(boolean objective, RatSignal cex, BooleanCtx hyp) {
		int index = index(objective);
		sat[index] = cex;
		cube[index] = hyp;
		super.sat(objective);
		if (satisfiable()) {
			rotateTarget(objective);
		} else {
			target[index(true)]  = RatSignal.uniformRandom(sat[index].size(),S);
			target[index(false)] = RatSignal.uniformRandom(sat[index].size(),S);
		}
	}
	
	public void unsat(boolean objective) {
		super.unsat(objective);
		if (satisfiable()) {
			rotateTarget(objective);
		}
		cube[index(objective)] = new BooleanCtx();
	}

	@Override
	public BooleanCtx hyp() {
		int index = index(objective());
		BooleanCtx hyp = cube[index];
/*		for (RatSignal src: pivot[index]) {
			System.out.println(ID.location() + id + ":" + "Pivot  : " + src);
			// Closer to the target ..
			String dot1Name = JFuzzName.pivotDot + (dotIndex++);
			IdExpr dot1ID = new IdExpr(dot1Name);
			ExprVect v = new ExprVect(S);
			Equation dot1 = new ExprSignal(dst.size(),v).sub(src).dot(dst.sub(src),dot1ID);
			hyp.define(dot1Name, NamedType.REAL, dot1);
			hyp.and(new BinaryExpr(dot1ID,BinaryOp.GREATER,Expr0));
			// Not too far ..
			String dot2Name = JFuzzName.pivotDot + (dotIndex++);
			IdExpr dot2ID = new IdExpr(dot2Name);	
			Equation dot2 = new ExprSignal(dst.size(),v).sub(dst).dot(src.sub(dst),dot2ID);
			hyp.define(dot2Name, NamedType.REAL, dot2);
			hyp.and(new BinaryExpr(dot2ID,BinaryOp.GREATEREQUAL,Expr0));
		}*/
		//System.out.println(ID.location() + "Hyp :" + hyp);
		return hyp;
	}

	@Override
	public RatSignal target() {
		return target[index(objective())];
	}
}
