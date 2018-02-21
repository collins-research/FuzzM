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

import jkind.lustre.BinaryOp;
import jkind.util.BigFraction;

public abstract class VariableRelation extends VariableBound {

	public AbstractPoly  poly;
	FeatureType feature;
	TargetType  target;
	// The value for this variable that is consistent with the Counter Example
	RelationType relation;

	protected VariableRelation(VariableID name, boolean cex, RelationType relation, AbstractPoly poly, FeatureType feature, TargetType target) {
		super(name,cex);
		this.relation = relation;
		this.poly = poly;
		this.feature = feature;
		this.target = target;
	}
	
	@Override
	public int countFeatures() {
		return (feature == FeatureType.FEATURE) ? 1 : 0;
	}
	
    @Override
    public boolean isArtifact() {
        return (feature != FeatureType.FEATURE);        
    }

	// abstract public VariableConstraint newConstraint(VariableID name, RelationType newInclusive, AbstractPoly poly, boolean cex);

	abstract protected String opString(VariableLocation location, String target);
	abstract protected String polyString();

	@Override
	public boolean isTarget() {
        return target == TargetType.TARGET;
    }

	abstract public VariableRelation setTarget(TargetType target);
	
	@Override
	public boolean implicitEquality() {
		return false;
	}
	
	@Override
	public Variable toEquality() {
		throw new IllegalArgumentException();
	}
	
	@Override
	public Set<VariableID> updateVariableSet(Set<VariableID> in) {
		return poly.updateVariableSet(in);
	}

	@Override
	public boolean reducableIntegerInterval() {
		return false;
	}

	@Override
	public RestrictionResult reducedInterval() {
		throw new IllegalArgumentException();
	}

	public BigFraction maxValue(int sign, Map<VariableID,BigFraction> ctx) {
		return poly.evaluate(ctx);
	}

	abstract public BinaryOp binaryOp();
	
}
