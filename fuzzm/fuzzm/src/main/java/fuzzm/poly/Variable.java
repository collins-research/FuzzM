/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.poly;

import java.util.Map;
import java.util.Set;

import fuzzm.util.Debug;
import fuzzm.util.ID;
import fuzzm.util.ProofWriter;
import fuzzm.value.poly.GlobalState;
import jkind.util.BigFraction;

abstract public class Variable implements VariableInterface {

	public final VariableID vid;
	public final boolean cex;
	
	public Variable(VariableID vid, boolean cex) {
	    assert(cex);
		this.vid = vid;
		this.cex = cex;
	}
	
	abstract public String toACL2();
	abstract public String toACL2(String vid);
    abstract public String cexString();

	protected String statusString() {
		return "(" + ((countFeatures() > 0) ? "*" : "") + ")";
	}
	
	abstract public int countFeatures();
	
	abstract public RestrictionResult andTrue(Variable arg);
	
	//abstract public Variable not();
	
	abstract public boolean implicitEquality();
	abstract public Variable toEquality();
	
	abstract public boolean requiresRestriction();
	abstract public RestrictionResult restriction();
	
	abstract public boolean slackIntegerBounds();
	abstract public Variable tightenIntegerBounds();

	abstract public boolean  reducableIntegerInterval();
	abstract public RestrictionResult reducedInterval();
	
	abstract protected RegionBounds constraintBounds(Map<VariableID,BigFraction> ctx);
	abstract protected RegionBounds constraintBounds();
    abstract protected RegionBounds intervalBounds(Map<VariableID,RegionBounds> ctx);

	
	// ACL2: (def::un better (x y)
	static Variable better(Variable c1, Variable c2) {
		if (c1.countFeatures() > c2.countFeatures()) return c1;
		if (c2.countFeatures() > c1.countFeatures()) return c2;
		if (GlobalState.oracle().nextBoolean()) {
			return c1;
		} else {
			return c2;
		}
	}	

	static Variable secondOnlyIfBetter(Variable c1, Variable c2) {
		if (c2.countFeatures() > c1.countFeatures()) return c2;
		return c1;
	}

	abstract public Set<VariableID> updateVariableSet(Set<VariableID> in);

	abstract public boolean evalCEX(Map<VariableID, BigFraction> ctx);

	abstract public Variable rewrite(Map<VariableID, AbstractPoly> rewrite);

	abstract public AbstractPoly maxBound(int sign);

	abstract public BigFraction maxValue(int sign, Map<VariableID,BigFraction> ctx);

    abstract public RestrictionResult mustContain(AbstractPoly v);

    abstract public boolean isTarget();
    
    abstract public boolean isArtifact();
    
    static RestrictionResult andTrue(Variable x, Variable y) {
        RestrictionResult res = x.andTrue(y);
        if (Debug.isEnabled()) {
            String xacl2 = x.toACL2();
            String yacl2 = y.toACL2();
            String racl2 = res.toACL2();
            ProofWriter.printRefinement(ID.location(), "andTrue", "(and "+xacl2+" "+yacl2+")", racl2);
            //ProofWriter.printAndTT(ID.location(),"andTrue",xacl2,yacl2, racl2); 
        }
        Variable z = res.newConstraint;
        assert(!(z.isTarget() && y.isTarget()) || z.isTarget());

        if ((x instanceof VariablePhantom) && (y instanceof VariablePhantom)) {
            assert(z instanceof VariablePhantom);
        } else if (x instanceof VariablePhantom) {
            
        } else if (y instanceof VariablePhantom) {
            
        }
        
        return res;
    }
    
    static Variable minSet(Variable x, Variable y) {
        Variable res = x.minSet(y);
        if (Debug.proof() && !(x instanceof VariablePhantom) && !(y instanceof VariablePhantom)) {
            String Xe = x.toACL2(",x");
            String Ye = y.toACL2(",x");
            String Ze = res.toACL2(",x");
            String Ce = "(and "+Xe+" "+Ye+")";
            //Debug.setEnabled(true);
            ProofWriter.printThm(ID.location(), "minSet", true, Ze, Ce);
            //Debug.setEnabled(false);
        }
        return res;
    }
    
    static Variable maxSet(Variable x, Variable y) {
        Variable res = x.maxSet(y);
        if (Debug.proof() && !(x instanceof VariablePhantom) && !(y instanceof VariablePhantom)) {
            String Xe = x.toACL2(",x");
            String Ye = y.toACL2(",x");
            String Ze = res.toACL2(",x");
            String Ce = "(or "+Xe+" "+Ye+")";
            //Debug.setEnabled(true);
            ProofWriter.printThm(ID.location(), "maxSet", true, Ce, Ze);
            //Debug.setEnabled(false);
        }
        return res;
    }
    
    
    static Variable target(Variable H, boolean trueH, Variable C, boolean trueC) {
        // We are keeping H.  If H implies not C, we target H.
        if (H.isTarget()) return H;
        Variable res = trueH ? C.target(trueC, H) : C.target(! trueC, H);        
        //Debug.setEnabled(true);        
        if ((!(H instanceof VariablePhantom)) && Debug.proof()) {
            String He = H.toACL2(",x");
            trueC = trueH ? trueC : ! trueC;
            if (C instanceof VariableInterval) {
                VariableInterval Ci = (VariableInterval) C;
                String Cl = Ci.lt.toACL2(",x");
                Cl = trueC ? Cl : "(not "+Cl+")";
                Cl = "(not "+Cl+")";
                String Cg = Ci.gt.toACL2(",x");
                Cg = trueC ? Cg : "(not "+Cg+")";
                Cg = "(not "+Cg+")";
                String Ce = res.isTarget() ? "(or " + Cl + " " + Cg + ")" : "(and " + Cl + " " + Cg + ")";
                ProofWriter.printThm(ID.location(), "target", res.isTarget(), He, Ce);
            } else {
                String Ce = C.toACL2(",x");
                Ce = trueC ? Ce : "(not "+Ce+")";
                Ce = "(not "+Ce+")";
                ProofWriter.printThm(ID.location(), "target", res.isTarget(), He, Ce);
            }
            //Debug.setEnabled(false);
        }
        return res;
    }
    
}
