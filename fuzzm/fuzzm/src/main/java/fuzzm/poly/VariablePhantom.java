/* 
 * Copyright (C) 2018, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.poly;

import java.util.Map;
import java.util.Set;

import jkind.util.BigFraction;

public class VariablePhantom extends VariableBound {

    // Phantom variables are created by andTF() when a True
    // variable constraint has no corresponding False constraint.
    // Phantom variables can be safely ignored during test generation.
    // Their only purpose in life is to help identify Target opportunities.
    //
    // DAG - it would be nice to have a tighter formal spec for phantom variables.
    //
    // DAG - I suspect that we will need to incorporate a negation bit to model
    //       multiple level phantom variables .. we saw examples of that in the
    //       dot arrow example after adding hyps.
    // 
    Variable v;
    boolean polarity;
    public VariablePhantom(Variable v) {
        super(v.vid, v.cex);
        if (v instanceof VariablePhantom) {
            this.v = ((VariablePhantom) v).v;
            this.polarity = ! ((VariablePhantom) v).polarity;
        } else {    
            this.v = v;
            this.polarity = false;
        }
    }
    
    @Override
    public RestrictionResult andTrue(Variable arg) {
        return arg.andTrue2(this);
    }
    @Override
    public RestrictionResult andTrue2(VariableEquality left) {
        Variable res = Variable.target(left, true, this.v, polarity);
        return new RestrictionResult(res);
    }
    @Override
    public RestrictionResult andTrue2(VariableInterval left) {
        Variable res = Variable.target(left, true, this.v, polarity);
        return new RestrictionResult(res);
    }
    @Override
    public RestrictionResult andTrue2(VariableLess left) {
        Variable res = Variable.target(left, true, this.v, polarity);
        return new RestrictionResult(res);
    }
    @Override
    public RestrictionResult andTrue2(VariableGreater left) {
        Variable res = Variable.target(left, true, this.v, polarity);
        return new RestrictionResult(res);
    }
    @Override
    public RestrictionResult andTrue2(VariableBoolean left) {
        Variable res = Variable.target(left, true, this.v, polarity);
        return new RestrictionResult(res);
    }
     
    @Override
    public Variable minSet(Variable right) {
        return right;
    }
    @Override
    public Variable minSet2(VariableEquality left) {
        return left;
    }
    @Override
    public Variable minSet2(VariableInterval left) {
        return left;
    }
    @Override
    public Variable minSet2(VariableLess left) {
        return left;
    }
    @Override
    public Variable minSet2(VariableGreater left) {
        return left;
    }
    @Override
    public Variable minSet2(VariableBoolean left) {
        throw new IllegalArgumentException();
    }
    @Override
    public Variable maxSet(Variable right) {
        return right;
    }
    @Override
    public Variable maxSet2(VariableEquality left) {
        return left;
    }
    @Override
    public Variable maxSet2(VariableInterval left) {
        return left;
    }
    @Override
    public Variable maxSet2(VariableLess left) {
        return left;
    }
    @Override
    public Variable maxSet2(VariableGreater left) {
        return left;
    }
    @Override
    public Variable maxSet2(VariableBoolean left) {
        throw new IllegalArgumentException();
    }
    @Override
    public Variable target(boolean trueL, Variable right) {
        return right.target2(! trueL, this);
    }
    @Override
    public Variable target2(boolean trueL, VariableEquality left) {
        // We need test cases for these .. I think v should be negated.
        return new VariablePhantom(Variable.target(v,polarity,left,!trueL));
    }
    @Override
    public Variable target2(boolean trueL, VariableInterval left) {
        return new VariablePhantom(Variable.target(v,polarity,left,!trueL));
    }
    @Override
    public Variable target2(boolean trueL, VariableLess left) {
        return new VariablePhantom(Variable.target(v,polarity,left,!trueL));
    }
    @Override
    public Variable target2(boolean trueL, VariableGreater left) {
        return new VariablePhantom(Variable.target(v,polarity,left,!trueL));
    }
    @Override
    public Variable target2(boolean trueL, VariableBoolean left) {
        throw new IllegalArgumentException();
    }
    @Override
    public String 
    toString() {
        return "PHI(" + v.toString() + ")";
    }
    @Override
    public String toACL2() {
        return "#+joe" + v.toACL2();
    }
    @Override
    public String toACL2(String cex) {
        return "#+joe" + v.toACL2(cex);
    }
    @Override
    public String cexString() {
        return "";
    }
    @Override
    public int countFeatures() {
        return 0;
    }
    @Override
    public boolean implicitEquality() {
        return false;
    }
    @Override
    public Variable toEquality() {
        throw new IllegalArgumentException();
    }
    @Override
    public boolean requiresRestriction() {
        return false;
    }
    @Override
    public RestrictionResult restriction() {
        throw new IllegalArgumentException();
    }
    @Override
    public boolean slackIntegerBounds() {
        return false;
    }
    @Override
    public Variable tightenIntegerBounds() {
        throw new IllegalArgumentException();
    }
    @Override
    public boolean reducableIntegerInterval() {
        return false;
    }
    @Override
    public RestrictionResult reducedInterval() {
        throw new IllegalArgumentException();
    }
    @Override
    protected RegionBounds constraintBounds(Map<VariableID, BigFraction> ctx) {
        throw new IllegalArgumentException();
    }
    @Override
    protected RegionBounds constraintBounds() {
        throw new IllegalArgumentException();
    }
    @Override
    protected RegionBounds intervalBounds(Map<VariableID, RegionBounds> ctx) {
        throw new IllegalArgumentException();
    }
    @Override
    public Set<VariableID> updateVariableSet(Set<VariableID> in) {
        throw new IllegalArgumentException();
    }
    @Override
    public boolean evalCEX(Map<VariableID, BigFraction> ctx) {
        throw new IllegalArgumentException();
    }
    @Override
    public Variable rewrite(Map<VariableID, AbstractPoly> rewrite) {
        return new VariablePhantom(v.rewrite(rewrite));
    }
    @Override
    public AbstractPoly maxBound(int sign) {
        throw new IllegalArgumentException();
    }
    @Override
    public BigFraction maxValue(int sign, Map<VariableID, BigFraction> ctx) {
        throw new IllegalArgumentException();
    }
    @Override
    public RestrictionResult mustContain(AbstractPoly v) {
        throw new IllegalArgumentException();
    }

    @Override
    public boolean isTarget() {
        return false;
    }

    @Override
    public RestrictionResult andTrue2(VariablePhantom left) {
        return new RestrictionResult(new VariablePhantom(Variable.maxSet(v,left.v)));
    }

    @Override
    public Variable minSet2(VariablePhantom left) {
        return new VariablePhantom(Variable.minSet(v,left.v));
    }

    @Override
    public Variable maxSet2(VariablePhantom left) {
        return new VariablePhantom(Variable.maxSet(v,left.v));
    }

    @Override
    public Variable target2(boolean trueL, VariablePhantom left) {
        return new VariablePhantom(Variable.target(this.v, this.polarity, left.v, (!trueL) ^ left.polarity));
    }

    @Override
    public boolean isArtifact() {
        return false;
    }

}
