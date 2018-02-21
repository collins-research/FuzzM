/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.heuristic;

import fuzzm.lustre.BooleanCtx;
import fuzzm.util.FuzzmName;
import fuzzm.util.ID;
import fuzzm.util.RatSignal;
import jkind.lustre.BoolExpr;
import jkind.lustre.Expr;
import jkind.lustre.IdExpr;
import jkind.lustre.UnaryExpr;
import jkind.lustre.UnaryOp;
/***
 * 
 * The SATMode tracks the known mode of a property based on previous
 * attempts to satisfy or falsify the property.  Presumably the
 * mode starts out NONE.  If the property can be satisfied, it will
 * be TRUE and if it can be falsified it will be FALSE.  If the
 * property can be both satisfied and falsified, the mode will be 
 * SAT, otherwise it will be UNSAT.
 *
 */
enum SATMode {
    NONE,
    TRUE,
    FALSE,
    SAT,
    UNSAT;

    private SATMode satTransition(boolean objective) {
    	switch (this) {
    	case NONE:
    		return objective ? TRUE : FALSE;
    	case TRUE:
    		return objective ? TRUE : SAT;
    	case FALSE:
    		return objective ? SAT  : FALSE;
    	default:
    		return this;
    	}
    }

    SATMode unsat(int id) {
    	switch (this) {
    	case SAT:
    		return this;
    	default:
    		System.out.println(ID.location() + "id:" + id + " is now UNSAT");
    		return UNSAT;
    	}
    }
    
    boolean satisfiable() {
    	return this.equals(SAT);
    }
    
    boolean ready() {
    	return ! this.equals(UNSAT);
    }

    public SATMode sat(int id, boolean objective) {
    	SATMode mode = satTransition(objective);
    	if (! this.equals(SAT)) {
    		System.out.println(ID.location() + "id:" + id + " is now " + mode);
    	}
    	return mode;
    }
}
/***
 * 
 * The fuzz heuristic alternates attempts to satisfy and falsify
 * a property.  It tracks the mode of the property to ensure that
 * the property is satisfiable.
 *
 */
public abstract class FuzzHeuristic implements HeuristicInterface {
	
	int id = -1;
	private SATMode mode = SATMode.NONE;
	boolean wait[] = { false, false };
	private boolean priority = true;
	private Expr property[] = { new BoolExpr(false), new BoolExpr(true)};
	
	public FuzzHeuristic() {
	}

	public FuzzHeuristic(int id, Expr property) {
		this.id = id;
		setProperty(property);
	}
	
	static int index(boolean objective) {
		return objective ? 1 : 0;
	}
	
	int index() {
		return index(objective());
	}
	
	public BooleanCtx hyp() {
		return new BooleanCtx();
	}
	
	public Expr prop() {
		assert(property != null);
		Expr prop = property[index()];
		System.out.println(ID.location() + "Prop : " + prop);
		return prop;
	}
	
	abstract public RatSignal target();
	
	public BooleanCtx constraint() {
		Expr prop = prop();
		BooleanCtx res = new BooleanCtx();
		return res.implies(prop);
	}	
	
	protected final void setProperty(Expr property) {
		this.property[index(true)] = property;
		this.property[index(false)] = new UnaryExpr(UnaryOp.NOT,property);
	}
	
	public Expr getProperty() {
		return property[index()];
	}
	
	protected void setPriority(boolean priority) {
		this.priority = priority;
	}
	
	private void unwait(boolean objective) {
		int index = index(objective);
		wait[index] = false;
	}
	
	public void wait(boolean objective) {
		int index = index(objective);
		wait[index] = true;
	}
	
	private boolean waiting(boolean objective) {
		return wait[index(objective)];
	}
	
	public boolean objective() {
		return waiting(priority) ? (! priority) : priority;
	}
	
	public boolean ready() {
		boolean readymode = mode.ready() && (! ((waiting(true) && waiting(false))));
		return readymode;
	}
	
	public boolean satisfiable() {
		return mode.satisfiable();
	}
	
	public void sat(boolean objective) {
		mode = mode.sat(id,objective);
		priority = waiting(objective) ? ! priority : priority;
		unwait(objective);
	}

	abstract public void sat(boolean objective, RatSignal cex, BooleanCtx hyp);
	
	public void unsat(boolean objective) {
		mode = mode.unsat(id);
		priority = waiting(objective) ? ! priority : priority;
		unwait(objective);
	}


}
