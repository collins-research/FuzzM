/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.heuristic;

import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.Queue;

import fuzzm.lustre.BooleanCtx;
import fuzzm.lustre.PolyConstraintCtx;
import fuzzm.lustre.generalize.PolyGeneralizationResult;
import fuzzm.lustre.generalize.ReMapExpr;
import fuzzm.poly.Variable;
import fuzzm.util.ID;
import fuzzm.util.IntervalVector;
import fuzzm.util.RatSignal;
import fuzzm.value.poly.GlobalState;
import jkind.lustre.Expr;

class ConstraintQueue {
    
    private Queue<BooleanCtx> constraintHistory  = new LinkedList<>();    
    private BooleanCtx allConstraints  = new BooleanCtx();

    public void popConstraint() {
        //allConstraints.printDecls(ID.location());
        if (constraintHistory.isEmpty()) return;
        @SuppressWarnings("unused")
        BooleanCtx drop = constraintHistory.poll();
        //drop.printDecls(ID.location());
        BooleanCtx res = new BooleanCtx();
        for (BooleanCtx b: constraintHistory) {
            res = res.and(b);
        }
        allConstraints = res;
        //allConstraints.printDecls(ID.location());
        return;
    }
    
    public void pushConstraint(BooleanCtx constraint) {
        //constraint.printDecls(ID.location());
        //allConstraints.printDecls(ID.location());
        constraintHistory.add(constraint);
        allConstraints = allConstraints.and(constraint);
        //allConstraints.printDecls(ID.location());
    }

    public boolean isEmpty() {
        return constraintHistory.isEmpty();
    }
    
    public BooleanCtx currentConstraint() {
        return allConstraints;
    }
    
}

class PossibleHistory  {

    ConstraintQueue cqueue = new ConstraintQueue();
    BooleanCtx pending = null;

    public void tryConstraint(BooleanCtx constraint) {
        //System.out.println(ID.location() + "tryConstraint()");
        //if (constraint != null) constraint.printDecls(ID.location());
        if (pending != null) {
            cqueue.pushConstraint(pending);
        }
        pending = constraint;
    }
    public void doConstraint(BooleanCtx constraint) {
        //System.out.println(ID.location() + "doConstraint()");
        //constraint.printDecls(ID.location());
        tryConstraint(null);
        cqueue.pushConstraint(constraint);
    }
    public boolean popConstraint() {
        //System.out.println(ID.location() + "popConstraint()");
        boolean justTrying = true;
        if (pending == null) {
            justTrying = false;
            cqueue.popConstraint();
        }
        pending = null;
        return justTrying;
    }
    public boolean isEmpty() {
        return (pending == null) && cqueue.isEmpty();
    }
    public BooleanCtx currentConstraint() {
        BooleanCtx res = cqueue.currentConstraint();
        if (pending == null) return res;
        return res.and(pending);
    }
}

class UNSATTracker {
    PossibleHistory history = new PossibleHistory();
    private boolean unsat = false;
    public BooleanCtx currentConstraint() {
        return history.currentConstraint();
    }
    public void unsat() {
        if (history.isEmpty()) {
            unsat = true;
            return;
        }
        history.popConstraint();
        return;
    }
    public boolean done() {
        return unsat;
    }    
}

class ProbeHeuristics extends UNSATTracker {
    int maxEphemeral       = 1;
    int remainingEphemeral = 0;
    private BooleanCtx doProposeHyp(List<Variable> targets, ReMapExpr remap) {
        remainingEphemeral = maxEphemeral;
        Collections.shuffle(targets);
        Variable target = targets.get(0);
        System.out.println(ID.location() + "Targeting : " + target.toString());
        return new PolyConstraintCtx(target,remap);
    }
    private BooleanCtx doSampleHyp(List<Variable> targets, List<Variable> artifacts, ReMapExpr remap) {
        int artifactCount = artifacts.size();
        int options = targets.size() + artifacts.size();
        maxEphemeral = maxEphemeral > artifactCount ? maxEphemeral : artifactCount;
        int min = remainingEphemeral < options ? remainingEphemeral : options;
        remainingEphemeral = (2*min + 5*remainingEphemeral)/8;
        double p = (artifactCount*1.0)/(options*1.0);
        List<Variable> src = (GlobalState.oracle().nextDouble() < p) ? artifacts : targets;
        Collections.shuffle(src);
        Variable target = src.get(0);
        System.out.println(ID.location() + "Sampling : " + target.toString());
        return new PolyConstraintCtx(target,remap);
    }
    protected void sat(PolyGeneralizationResult res) {
        List<Variable> targets   = res.result.getTargets();
        List<Variable> artifacts = res.result.getArtifacts();
        if (targets.isEmpty() && artifacts.isEmpty()) {
            history.popConstraint();
        } else {
            BooleanCtx constraint;
            if (artifacts.isEmpty() || ((! targets.isEmpty()) && (remainingEphemeral == 0))) {
                constraint = doProposeHyp(targets,res.remap);
                history.doConstraint(constraint);
            } else {
                constraint = doSampleHyp(targets,artifacts,res.remap);
                history.tryConstraint(constraint);
            }
        }
        return;
    }
}

class HistoryHeuristics extends ProbeHeuristics {
    int initializations = 0;
    int k0 = -1;
    double ktime0 = -1.0;
    private void updateStats(int k, double ktime) {
        if (initializations == 0) {
            k0 = k;
            ktime0 = ktime;            
        } else {
            ktime0 = (ktime0*initializations + ktime)/(initializations + 1.0);
        }
        initializations += (initializations >= 99) ? 0 : 1;
    }
    public void sat(int k, double ktime, PolyGeneralizationResult res) {
        updateStats(k,ktime);
        if ((k != k0) || (ktime >= 1.2*ktime0)) {
            boolean justTrying = history.popConstraint();
            if (! justTrying) return;
        }
        super.sat(res);
    }
}
class BoundHistory extends HistoryHeuristics {
    int count;
    public BoundHistory(int count) {
        this.count = count;
    }
    private void countDown() {
        count = (count <= 0) ? count : count - 1;
    }
    public void sat(int k, double ktime, PolyGeneralizationResult res) {
        countDown();
        super.sat(k,ktime,res);
    }
    public void unsat() {
        countDown();
        super.unsat();
    }
    @Override
    public boolean done() {
        return (count == 0) || super.done();
    }
}

public class PropertyHeuristic implements HeuristicInterface {

    final String name;
    RatSignal lastCounterExample = new RatSignal();
	boolean ready = true;
	IntervalVector S;
	Expr constraint;
	BoundHistory history;
	
	public PropertyHeuristic(IntervalVector S, String name, Expr constraint, int count) {
	    this.name = name;
		this.constraint = constraint;
		this.S = S;
		//this.currHyp = new BooleanCtx();
		this.history = new BoundHistory(count);
	}
	
    @Override
    public String name() {
        return name;
    }
    
	@Override
	public boolean objective() {
		return false;
	}

	@Override
	public BooleanCtx hyp() {
		BooleanCtx res = history.currentConstraint();
		//res.printDecls(ID.location());
		return res;
	}

	@Override
	public BooleanCtx constraint() {
		return new BooleanCtx(constraint);
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
		return ready && (! history.done());
	}

	@Override
	public void sat(boolean objective, double time, RatSignal counterExample, PolyGeneralizationResult res) {
        lastCounterExample = counterExample;
        ready = true;
        int k = counterExample.size();
		history.sat(k,time/k,res);
	}

	@Override
	public void unsat(boolean objective) {
        ready = true;
		history.unsat();
	}

    @Override
    public boolean done() {
        return history.done();
    }

}
