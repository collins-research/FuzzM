/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.poly;

import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import fuzzm.lustre.evaluation.PolyFunctionMap;
import fuzzm.solver.SolverResults;
import fuzzm.util.Debug;
import fuzzm.util.ID;
import fuzzm.util.IntervalVector;
import fuzzm.util.ProofWriter;
import fuzzm.util.RatSignal;
import fuzzm.util.TypedName;
import jkind.util.BigFraction;

abstract public class PolyBool {

	public static final PolyBool TRUE  = new TruePolyBool(true,new VariableList());
	public static final PolyBool FALSE = new FalsePolyBool(false,new VariableList());
	
	public boolean cex;
	final VariableList body;
	
	@Override
	abstract public String toString();
	
	abstract public String toACL2();
	
	protected PolyBool() {
		this.body = new VariableList();
		this.cex = true;
	}
	
	protected PolyBool(VariableList body) {
		this.body = body;
		this.cex = true;
		for (Variable v: body) {
			this.cex &= v.cex;
		}
	}
	
	protected PolyBool(boolean cex, VariableList body) {
		this.body = body;
		this.cex = cex;
	}
	
	protected PolyBool(Variable c) {
		this.body = new VariableList(c);
		this.cex = c.cex;
	}
	
	public static PolyBool boolVar(VariableBoolean c) {
	    return c.isNegated() ? new FalsePolyBool(c) : new TruePolyBool(c);
	}
	
	public static PolyBool less0(AbstractPoly arg) {
		//
		// We need to normalize these expressions immediately.
		//
		// Ax + poly < 0
		//if (Debug.isEnabled()) System.out.println(ID.location() + "less0 : (" + arg + ") < 0");
		if (arg.isConstant()) {
			return (arg.getConstant().signum() < 0) ? TRUE : FALSE;
		}
		PolyBool res = VariableBound.normalizePolyLess0(arg, RelationType.EXCLUSIVE, FeatureType.FEATURE, TargetType.CHAFF);
		if (Debug.proof()) {
		    ProofWriter.printRefinement(ID.location(),"less0","(< " + arg.toACL2() + " 0)" , res.toACL2());
		}
		return res;
	}
	
	public static PolyBool greater0(AbstractPoly arg) {
		//if (Debug.isEnabled()) System.out.println(ID.location() + "greater0 : (" + arg + ") > 0");
		// x + poly > 0
		if (arg.isConstant()) {
			return (arg.getConstant().signum() > 0) ? TRUE : FALSE;
		}
		PolyBool res = VariableBound.normalizePolyGreater0(arg, RelationType.EXCLUSIVE, FeatureType.FEATURE, TargetType.CHAFF);
		if (Debug.proof()) {
            ProofWriter.printRefinement(ID.location(),"greater0","(< 0 " + arg.toACL2() + ")" , res.toACL2());
        }
        return res;
	}
	
	public static PolyBool equal0(AbstractPoly arg) {
		//System.out.println(ID.location() + "equal0(" + arg + ")");
		if (arg.isConstant()) {
			return (arg.getConstant().signum() == 0) ? TRUE : FALSE;
		}
		PolyBool res = VariableBound.normalizePolyEquality0(arg, FeatureType.FEATURE, TargetType.CHAFF);
		if (Debug.proof()) {
            ProofWriter.printRefinement(ID.location(),"equal0","(= 0 " + arg.toACL2() + ")" , res.toACL2());
        }
        return res;
	}
	
//	private int features() {
//		int res = 0;
//		for (Variable vc: body) {
//			res += vc.countFeatures();
//		}
//		return res;
//	}

	private static PolyBool and_true(PolyBool x, PolyBool y) {
	    // If either input were negated, they would evaluate to false.
	    assert(! x.isNegated());
	    assert(! y.isNegated());
		VariableList xbody = x.body;
		VariableList ybody = y.body;
		PolyBool res = new TruePolyBool(x.cex && y.cex,VariableList.andTT(xbody,ybody));
		return res;
	}
	
	private static PolyBool and_false(PolyBool x, PolyBool y) {
	    assert(x.isNegated() && y.isNegated());
		PolyBool res = new FalsePolyBool(x.cex || y.cex,VariableList.andFF(x.body,y.body));
		if (Debug.isEnabled()) 
            System.out.println(ID.location() + "andFalse: (" + x + " and "+ y + ") = " + res);       
        return res;
	}
	
    private static PolyBool and_true_false(PolyBool x, PolyBool y) {
        assert(! x.isNegated() && y.isNegated());
        PolyBool res = new FalsePolyBool(! x.cex || y.cex,VariableList.andTF(x.body,y.body));
        if (Debug.isEnabled()) 
            System.out.println(ID.location() + "andTrueFalse: (" + x + " and "+ y + ") = " + res);       
        return res;
    }
    
	private static PolyBool and(PolyBool x, PolyBool y) {
	    //System.out.println(ID.location() + "x = " + x);
	    //System.out.println(ID.location() + "y = " + y);
        if (x.isAlwaysTrue())  return y;
		if (y.isAlwaysTrue())  return x;
		if (x.isAlwaysFalse() || y.isAlwaysFalse()) return PolyBool.FALSE;
		PolyBool res;
		if (x.cex) {
			if (y.cex) {
				res = and_true(x,y);
			} else {
			    res = and_true_false(x,y);
			}
		} else if (y.cex) {
			res = and_true_false(y,x);
		} else {
			res = and_false(x,y);
		}
		if (Debug.isEnabled()) {
		    System.out.println(ID.location() + "and(" + x + "," + y + ") =" + res);
		}
		//Debug.setProof(true);
        if (Debug.proof()) {
            ProofWriter.printRefinement(ID.location(),"and","(and " + x.toACL2() + y.toACL2() + ")", res.toACL2());
		}
		//Debug.setProof(false);
		return res;
	}
	
	public abstract boolean isNegated();
	public abstract boolean isAlwaysFalse();
	public abstract boolean isAlwaysTrue();
	
	abstract public PolyBool not();	
	public PolyBool and(PolyBool arg) {
		PolyBool res = and(this,arg);
		if (Debug.isEnabled()) System.out.println(ID.location() + this.bytes() + " and " + arg.bytes() + " := " + res.bytes());
		return res;
	}
	
	public PolyBool or(PolyBool arg) {
		PolyBool res = and(this.not(),arg.not());
		res = res.not();
		if (Debug.isEnabled()) System.out.println(ID.location() + this.bytes() + " or " + arg.bytes() + " := " + res.bytes());
		return res;
	}
	
	public PolyBool iff(PolyBool value) {
	    // (iff a b) = (or (and a b) (and (not a) (not b)))
        PolyBool a = this;
        PolyBool b = value;
        PolyBool m1 = and(a,b);
        PolyBool m2 = and(a.not(),b.not());        
	    //System.out.println(ID.location() + "a = " + a);
	    //System.out.println(ID.location() + "b = " + b);
	    PolyBool res = m1.or(m2);
//	    if (a.cex && b.cex) {
//	        //System.out.println(ID.location() + "case 1: TT");
//	        res = and(a,b);
//	    } else if (!a.cex && !b.cex) {
//	        //System.out.println(ID.location() + "case 2: FF");
//	        a = a.not();
//	        b = b.not();
//            res = and(a,b);
//	    } else if (a.cex && !b.cex) {
//	        //System.out.println(ID.location() + "case 3: TF");
//            res = and(a,b.not()).not();
//	    } else {
//	        //System.out.println(ID.location() + "case 4: FT");
//            res = and(a.not(),b).not();
//	    }
		//System.out.println(ID.location() + "iff = " + res);
		return res;
	}

	abstract public List<Variable> getArtifacts();
	
    abstract public List<Variable> getTargets();
    
	public RatSignal randomVector(boolean biased, BigFraction min, BigFraction max, IntervalVector span, Map<VariableID,BigFraction> ctx) {
	    assert(cex && !isNegated());
		RatSignal res;
		try {
		    res = body.randomVector(biased, min, max, span, ctx);
		} catch (Throwable t) {
		    System.err.println(ID.location() + "*** Failing Example " + this.toString());
		    throw t;
		}
		return res;
	}
	
//	public static PolyBool range(VariableID v, BigFraction min, BigFraction max) {
//		PolyBase minP = new PolyBase(min);
//		PolyBase maxP = new PolyBase(max);
//		VariableGreater gt = new VariableGreater(v,v.cex.compareTo(min) >= 0,RelationType.INCLUSIVE,minP,FeatureType.FEATURE);
//		VariableLess    lt = new VariableLess(v,v.cex.compareTo(max) <= 0,RelationType.INCLUSIVE,maxP,FeatureType.FEATURE);
//		return new TruePolyBool(new VariableInterval(gt,lt));
//	}

	abstract public PolyBool normalize();

	public int bytes() {
		return body.size();
	}

	public Collection<VariableID> unboundVariables() {
		return body.unboundVariables();
	}

	public Map<TypedName,RegionBounds> intervalBounds() {
		Map<VariableID,RegionBounds> r1 = body.intervalBounds();
		Map<TypedName,RegionBounds> res = new HashMap<>();
		for (VariableID vid: r1.keySet()) {
			TypedName name = vid.name.name;
			if (! res.containsKey(name)) {
				res.put(name, r1.get(vid));
			} else {
				res.put(name, r1.get(vid).union(res.get(name)));
			}
		}
		return res;
	}

	abstract public SolverResults optimize(SolverResults cex, PolyFunctionMap fmap, RatSignal target);
	
}
