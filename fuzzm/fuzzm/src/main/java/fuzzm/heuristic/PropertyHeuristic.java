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
import jkind.lustre.UnaryExpr;
import jkind.lustre.UnaryOp;

public class PropertyHeuristic implements HeuristicInterface {

    final String name;
    RatSignal lastCounterExample = new RatSignal();
	boolean ready = true;
	boolean unsat = false;
	IntervalVector S;
	Expr prop;
	BooleanCtx currHyp;
	int count = -1;

	public PropertyHeuristic(IntervalVector S, String name, Expr prop, int count) {
	    this.name = name;
		this.prop = new UnaryExpr(UnaryOp.NOT,prop);
		this.S = S;
		this.currHyp = new BooleanCtx();
		this.count = count;
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
		return currHyp;
	}

	@Override
	public BooleanCtx constraint() {
		BooleanCtx res = new BooleanCtx();
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
	public void sat(boolean objective, double time, RatSignal counterExample, PolyGeneralizationResult res) {
        lastCounterExample = counterExample;
        ready = true;
		currHyp = satBounds(time, counterExample.size(),res);
	}

	@Override
	public void unsat(boolean objective) {
        ready = true;
		currHyp = unsatBounds();
	}
	
	Queue<BooleanCtx> history  = new LinkedList<>();	
    BooleanCtx savedHyps       = new BooleanCtx();

    BooleanCtx lastConstraint  = new BooleanCtx();
    boolean    lastIsProposed  = false;
    
    int maxEphemeral       = 1;
    int remainingEphemeral = 0;
    
    private BooleanCtx popHistory() {
        history.poll();
        BooleanCtx res = new BooleanCtx();
        for (BooleanCtx b: history) {
            res = res.and(b);
        }
        savedHyps = res;
        return res;
    }
    
    private BooleanCtx pushHistory() {
        history.add(lastConstraint);
        savedHyps = currHyp;
        return savedHyps;
    }
    
    private boolean excessiveHistory(int k, double time, List<Variable> targets, List<Variable> artifacts) {
        if (history.isEmpty()) return false;
        if (targets.isEmpty() && artifacts.isEmpty()) return true;
        if (k > k0) return true;
        if (time >= 2.0*k0) return true;
        // history.size()
        return false;
    }
    
    public boolean exploreCurrentState(boolean xhistory, List<Variable> targets, List<Variable> artifacts) {
        if (targets.isEmpty()) return true;
        if (remainingEphemeral == 0) return false;
        return true;
    }
    
    private BooleanCtx doProposeHyp(List<Variable> targets, ReMapExpr remap) {
        lastIsProposed = true;
        remainingEphemeral = maxEphemeral;
        Collections.shuffle(targets);
        Variable target = targets.get(0);
        System.out.println(ID.location() + "Targeting : " + target.toString());
        return new PolyConstraintCtx(target,remap);
    }
    
    private BooleanCtx doSampleHyp(List<Variable> targets, List<Variable> artifacts, ReMapExpr remap) {
        lastIsProposed = false;
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
    
    private BooleanCtx doBackStep() {
        remainingEphemeral = maxEphemeral;
        lastIsProposed = false;
        return new BooleanCtx();
    }
    
    private boolean aKeeper(int k, double time) {
        return lastIsProposed && (k == k0) & (time < 2.0*t0);
    }
    
    private boolean backTrack(int k, double time, List<Variable> targets, List<Variable> artifacts) {
        return (k > k0) || (time >= 2.0*t0) || (targets.isEmpty() && artifacts.isEmpty());
    }
    
    private static double average(double t1, double t2) {
        return (99.0*t1 + t2)/100.0;
    }
    
    int    k0 = -1;
    double t0 = -1.0; 
    
    boolean countDown() {
        count = (count < 0) ? -1 : count-1;
        if (count == 0) {
            unsat = true;
            ready = false;
            return true;
        }        
        return false;        
    }
    
    BooleanCtx satBounds(double time, int k, PolyGeneralizationResult res) {
        if (countDown()) return new BooleanCtx();
        k0 = (k0 < 0) ? k : k0;
        t0 = (t0 < 0.0) ? time : ((k == k0) ? average(t0,time) : t0);
        if (aKeeper(k,time)) {
            pushHistory();
        }
        List<Variable> targets   = res.result.getTargets();
        List<Variable> artifacts = res.result.getArtifacts();
        boolean xhistory = excessiveHistory(k,time,targets,artifacts);
        if (xhistory) {
            popHistory();
        }
        if (backTrack(k,time,targets,artifacts)) {
            lastConstraint = doBackStep();
        } else {
            if (exploreCurrentState(xhistory,targets,artifacts)) {
                lastConstraint = doSampleHyp(targets,artifacts,res.remap);
            } else {
                lastConstraint = doProposeHyp(targets,res.remap);
            }
        }
        return savedHyps.and(lastConstraint);
    }

    private BooleanCtx doFailure() {
        unsat = true;
        ready = false;
        return new BooleanCtx();
    }
    
    private boolean unsatFailure() {
        return (lastConstraint == null);
    }
    
    private BooleanCtx doBackoffHyps() {
        BooleanCtx res = new BooleanCtx();
        if (! history.isEmpty()) {
            res = popHistory();
            res = res.and(lastConstraint);
        } else {            
            res = lastConstraint;
            lastConstraint = null;
        }
        lastIsProposed = (lastConstraint != null);
        return res;
    }
    
    BooleanCtx unsatBounds() {
        if (countDown()) return new BooleanCtx();
        if (unsatFailure()) {
            return doFailure();
        }
        return doBackoffHyps();
    }

    @Override
    public boolean isUNSAT() {
        return unsat;
    }

}
