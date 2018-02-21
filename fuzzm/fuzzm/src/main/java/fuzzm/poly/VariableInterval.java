/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.poly;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import fuzzm.util.ID;
import fuzzm.util.Rat;
import fuzzm.value.instance.RationalValue;
import jkind.lustre.NamedType;
import jkind.util.BigFraction;

public class VariableInterval extends VariableBound {

	VariableGreater gt;
	VariableLess    lt;
	
	protected VariableInterval(VariableGreater gt, VariableLess lt) {
		super(gt.vid,gt.cex && lt.cex);
		assert(gt.vid.compareTo(lt.vid) == 0);
		this.gt = gt;
		this.lt = lt;
	}

	
	@Override
	public int countFeatures() {
		return gt.countFeatures() + lt.countFeatures();
	}

	@Override
	public String toACL2() {
		return "(and " + gt.toACL2() + " " + lt.toACL2() + ")";
	}

    @Override
    public String toACL2(String cex) {
        return "(and " + gt.toACL2(cex) + " " + lt.toACL2(cex) + ")";
    }

	@Override
	public String toString() {
		return gt.statusString() + gt.polyString() + gt.opString(VariableLocation.RIGHT,gt.target.toString()) + vid + lt.opString(VariableLocation.LEFT,lt.target.toString()) + lt.polyString() + lt.statusString();
	}

	@Override
	public String cexString() {
		return "(" + gt.cexString() + "&&" + lt.cexString() + ")";
	}

//	@Override
//	protected VariableConstraint newConstraint() {
//		return new VariableRegion(gt,lt,op);
//	}

	@Override
	public RestrictionResult andTrue(Variable x) {
		assert(x.cex && this.cex);
		return ((VariableInterface) x).andTrue2(this);
	}

	@Override
	public RestrictionResult andTrue2(VariableEquality left) {
		return left.andTrue2(this);
	}

	// ACL2: (def::trueAnd andTrue-variableInterval-variableInterval (x y cex)
	@Override
	public RestrictionResult andTrue2(VariableInterval left) {
		VariableInterval right = this;
		RestrictionResult gt = restrictInequality(left.gt,right.gt);
		RestrictionResult lt = restrictInequality(left.lt,right.lt);
		return RestrictionResult.restrictionInterval(gt,lt);
	}

	// ACL2: (def::trueAnd andTrue-variableInterval-variableLess (x y cex)
	@Override
	public RestrictionResult andTrue2(VariableLess left) {
		RestrictionResult res = restrictInequality(left,lt);
		VariableLess less = (VariableLess) res.newConstraint;		
		return new RestrictionResult(new VariableInterval(gt,less),res.restrictionList);
	}

	@Override
	// ACL2: (def::trueAnd andTrue-variableInterval-variableGreater (x y cex)
	public RestrictionResult andTrue2(VariableGreater left) {
		RestrictionResult res = restrictInequality(left,gt);
		VariableGreater greater = (VariableGreater) res.newConstraint;	
		return new RestrictionResult(new VariableInterval(greater,lt),res.restrictionList);
	}

	@Override
	public boolean requiresRestriction() {
		AbstractPoly diff = lt.poly.subtract(gt.poly);
		return ! diff.isConstant();
	}

	@Override
	public RestrictionResult restriction() {
		AbstractPoly diff = lt.poly.subtract(gt.poly);
		return new RestrictionResult(this,VariableBound.solvePolyGreater0(diff, RelationType.INCLUSIVE,true,FeatureType.NONFEATURE,lt.target.inherit(gt.target)));
	}
	
	@Override
	protected RegionBounds constraintBounds(Map<VariableID, BigFraction> ctx) {
		RationalValue lower = new RationalValue(this.gt.poly.evaluate(ctx));
		RationalValue upper = new RationalValue(this.lt.poly.evaluate(ctx));
		return new RegionBounds(lower,this.gt.relation,upper,this.lt.relation);
	}

    @Override
    protected RegionBounds constraintBounds() {
        RationalValue lower = new RationalValue(this.gt.poly.evaluateCEX());
        RationalValue upper = new RationalValue(this.lt.poly.evaluateCEX());
        return new RegionBounds(lower,this.gt.relation,upper,this.lt.relation);
    }

	@Override
	protected RegionBounds intervalBounds(Map<VariableID,RegionBounds> ctx) {
		RegionBounds lower = this.gt.intervalBounds(ctx);
		RegionBounds upper = this.lt.intervalBounds(ctx);
		return lower.intersect(upper);
	}
	
	@Override
	public RestrictionResult andTrue2(VariableBoolean left) {
		throw new IllegalArgumentException();
	}

	@Override
	public boolean implicitEquality() {
		AbstractPoly diff = lt.poly.subtract(gt.poly);
		if (diff.isConstant()) {
			BigFraction delta = diff.getConstant();
			if (delta.signum() == 0) {
				return (gt.relation == RelationType.INCLUSIVE) && (lt.relation == RelationType.INCLUSIVE);
			} else if (vid.name.name.type == NamedType.INT) {
				if (delta.compareTo(BigFraction.ONE) < 0) {
					AbstractPoly base = gt.poly.subtract(gt.poly.getConstant());
					BigInteger z = base.leastCommonDenominator();
					if (z.compareTo(BigInteger.ONE) == 0) {
						return (delta.compareTo(BigFraction.ONE) < 0);
					}
				}
			}
		}
		return false;
	}

	@Override
	public Variable toEquality() {
		assert(implicitEquality());
		AbstractPoly diff = lt.poly.subtract(gt.poly);		
		BigFraction delta = diff.getConstant();
		FeatureType newFeature = gt.feature == lt.feature ? gt.feature : FeatureType.NONFEATURE;
		TargetType newTarget = gt.target == lt.target ? gt.target : TargetType.TARGET;
		if (delta.signum() == 0) {
			return new VariableEquality(vid,cex,gt.poly,newFeature, newTarget);
		} else {
			BigFraction min = Rat.roundUp(gt.poly.getConstant());
			BigFraction max = Rat.roundDown(lt.poly.getConstant());
			if (min.compareTo(max) != 0) {
				System.out.println(ID.location() + this);
				System.out.println(ID.location() + gt.poly.getConstant() + " <= " + lt.poly.getConstant());
				System.out.println(ID.location() + min + " <= " + max);
				System.exit(1);
			}
			AbstractPoly base = gt.poly.subtract(gt.poly.getConstant()).add(min);
			return new VariableEquality(vid,cex,base,newFeature,newTarget);
		}
	}


	@Override
	public Set<VariableID> updateVariableSet(Set<VariableID> in) {
		in = lt.updateVariableSet(in);
		in = gt.updateVariableSet(in);
		return in;
	}


	@Override
	public boolean slackIntegerBounds() {
		return lt.slackIntegerBounds() || gt.slackIntegerBounds();
	}


	@Override
	public Variable tightenIntegerBounds() {
		VariableGreater gt = (VariableGreater) (this.gt.slackIntegerBounds() ? this.gt.tightenIntegerBounds() : this.gt);
		VariableLess    lt = (VariableLess)    (this.lt.slackIntegerBounds() ? this.lt.tightenIntegerBounds() : this.lt);
		return new VariableInterval(gt,lt);
	}

	@Override
	public boolean evalCEX(Map<VariableID, BigFraction> ctx) {
		return gt.evalCEX(ctx) && lt.evalCEX(ctx);
	}


	@Override
	public boolean reducableIntegerInterval() {
		if (lt.relation == RelationType.EXCLUSIVE || gt.relation == RelationType.EXCLUSIVE) return false;
		boolean integerInterval = (vid.name.name.type == NamedType.INT) && !lt.poly.isConstant() && !gt.poly.isConstant();
		if (! integerInterval) return false;
		VariableID LTvid = lt.poly.leadingVariable();
        VariableID GTvid = gt.poly.leadingVariable();
        int cmp = LTvid.compareTo(GTvid);
        if (cmp != 0) return false;
        boolean rationalBounds = lt.poly.leastCommonDenominator().compareTo(BigInteger.ONE) > 0 &&
								 gt.poly.leastCommonDenominator().compareTo(BigInteger.ONE) > 0;
		return rationalBounds;
	}


	private boolean useLT() {
		VariableID LTvid = lt.poly.leadingVariable();
		VariableID GTvid = gt.poly.leadingVariable();
		// LTvid == GTvid
		BigInteger LTA = lt.poly.leastCommonDenominator();
		BigInteger GTA = gt.poly.leastCommonDenominator();
		BigInteger C  = lt.poly.getCoefficient(LTvid).multiply(LTA).getNumerator().abs();
		BigInteger E  = gt.poly.getCoefficient(GTvid).multiply(GTA).getNumerator().abs();
		LTA = LTA.divide(LTA.gcd(C));
		GTA = GTA.divide(GTA.gcd(E));
		return (LTA.compareTo(GTA) <= 0);
	}
	
	@Override
	public RestrictionResult reducedInterval() {
		assert(reducableIntegerInterval());
		if (useLT()) {
			// x <= lt.poly
			BigInteger N = lt.poly.leastCommonDenominator();
			BigFraction diff = lt.poly.evaluateCEX().subtract(vid.cex);
			BigFraction delta0 = diff.multiply(N);
			assert(delta0.getDenominator().compareTo(BigInteger.ONE) == 0);
			// This still isn't right ..
			VariableID delta = lt.poly.leadingVariable().afterAlloc("delta", NamedType.INT, delta0);
			//System.out.println(ID.location() + delta + " allocated after " + lt.poly.leadingVariable());
			//VariableID delta = VariableID.postAlloc("in", NamedType.INT, delta0);
			AbstractPoly eqpoly = lt.poly.subtract(new PolyBase(delta).divide(new BigFraction(N)));
			VariableGreater deltaBound = new VariableGreater(delta, true, RelationType.INCLUSIVE, new PolyBase(BigFraction.ZERO), lt.feature, lt.target);
			List<Variable> restrictions = new ArrayList<>();
			eqpoly = VariableEquality.integerEqualityConstraint(eqpoly,TargetType.CHAFF,restrictions);
			assert(eqpoly.evaluateCEX().compareTo(vid.cex) == 0);
			VariableEquality newBound = new VariableEquality(vid,true,eqpoly,lt.feature,lt.target);
			// gt.poly <= xeq
			AbstractPoly gtpoly = gt.poly.subtract(eqpoly);
			VariableBound newGT = VariableBound.solvePolyLess0(gtpoly, RelationType.INCLUSIVE, true, gt.feature, gt.target);
			restrictions.add(newGT);
			restrictions.add(deltaBound);
			return new RestrictionResult(newBound,restrictions);
		} else {
			BigInteger N = gt.poly.leastCommonDenominator();
			BigFraction diff = vid.cex.subtract(gt.poly.evaluateCEX());
			BigFraction delta0 = diff.multiply(N);
			assert(delta0.getDenominator().compareTo(BigInteger.ONE) == 0);
			VariableID delta = gt.poly.leadingVariable().afterAlloc("delta", NamedType.INT, delta0);
			//System.out.println(ID.location() + delta + " allocated after " + gt.poly.leadingVariable());
			//VariableID delta = VariableID.postAlloc("delta", NamedType.INT, delta0);
			AbstractPoly eqpoly = gt.poly.add(new PolyBase(delta).divide(new BigFraction(N)));
			VariableGreater deltaBound = new VariableGreater(delta, true, RelationType.INCLUSIVE, new PolyBase(BigFraction.ZERO), gt.feature, gt.target);
			List<Variable> restrictions = new ArrayList<>();
			eqpoly = VariableEquality.integerEqualityConstraint(eqpoly,TargetType.CHAFF,restrictions);
			assert(eqpoly.evaluateCEX().compareTo(vid.cex) == 0);
			VariableEquality newBound = new VariableEquality(vid,true,eqpoly,gt.feature,gt.target);
			// xeq <= lt.poly
			AbstractPoly ltpoly = eqpoly.subtract(lt.poly);
			VariableBound newLT = VariableBound.solvePolyLess0(ltpoly, RelationType.INCLUSIVE, true, lt.feature, lt.target);
			restrictions.add(newLT);
			restrictions.add(deltaBound);
			return new RestrictionResult(newBound,restrictions);			
		}
	}


	@Override
	public VariableInterval rewrite(Map<VariableID, AbstractPoly> rewrite) {
		return new VariableInterval(gt.rewrite(rewrite),lt.rewrite(rewrite));
	}
	@Override
	public AbstractPoly maxBound(int sign) {
		if (sign > 0) {
			return lt.poly.negate();
		}
		if (sign < 0) {
			return gt.poly;
		}
		return new PolyBase(BigFraction.ZERO);
	}

	@Override
	public BigFraction maxValue(int sign, Map<VariableID,BigFraction> ctx) {
		if (sign < 0) {
			return gt.poly.evaluate(ctx);
		}
		return lt.poly.evaluate(ctx);
	}

    @Override
    public RestrictionResult mustContain(AbstractPoly v) {
        List<Variable> restrictions = new ArrayList<>();
        restrictions.addAll(gt.mustContain(v).restrictionList);
        restrictions.addAll(lt.mustContain(v).restrictionList);
        return new RestrictionResult(this,restrictions);
    }


    @Override
    public Variable target(boolean trueL, Variable right) {
        return right.target2(!trueL, this);
    }

    @Override
    public Variable target2(boolean trueL, VariableEquality left) {
        return new VariableInterval((VariableGreater) this.gt.target2(trueL,left),(VariableLess) this.lt.target2(trueL,left));
    }


    @Override
    public Variable target2(boolean trueL, VariableInterval left) {
        if (trueL) {
            return new VariableInterval((VariableGreater) this.gt.target2(trueL,left.gt),(VariableLess) this.lt.target2(trueL,left.lt));
        } else {
            return new VariableInterval((VariableGreater) this.gt.target2(trueL,left.lt),(VariableLess) this.lt.target2(trueL,left.gt));            
        }
    }


    @Override
    public Variable target2(boolean trueL, VariableLess left) {
        if (trueL) {
            return new VariableInterval(this.gt,(VariableLess) this.lt.target2(trueL,left));
        } else {
            return new VariableInterval((VariableGreater) this.gt.target2(trueL,left),this.lt);            
        }
    }


    @Override
    public Variable target2(boolean trueL, VariableGreater left) {
        if (trueL) {
            return new VariableInterval((VariableGreater) this.gt.target2(trueL,left),this.lt);            
        } else {
            return new VariableInterval(this.gt,(VariableLess) this.lt.target2(trueL,left));
        }
    }


    @Override
    public Variable target2(boolean trueL, VariableBoolean left) {
        throw new IllegalArgumentException();
    }

    @Override
    public Variable minSet(Variable right) {
        return right.minSet2(this);
    }


    @Override
    public Variable minSet2(VariableEquality left) {
        return left;
    }


    @Override
    public Variable minSet2(VariableInterval left) {
        return new VariableInterval((VariableGreater) this.gt.minSet2(left.gt),(VariableLess) this.lt.minSet2(left.lt));
    }


    @Override
    public Variable minSet2(VariableLess left) {
        return new VariableInterval(this.gt,(VariableLess) this.lt.minSet2(left));
    }


    @Override
    public Variable minSet2(VariableGreater left) {
        return new VariableInterval((VariableGreater) this.gt.minSet2(left),this.lt);
    }


    @Override
    public Variable minSet2(VariableBoolean left) {
        throw new IllegalArgumentException();
    }

    @Override
    public boolean isTarget() {
        return lt.isTarget() || gt.isTarget();
    }


    @Override
    public boolean isArtifact() {
        return lt.isArtifact() || gt.isArtifact();
    }


    @Override
    public Variable maxSet(Variable right) {
        return right.maxSet2(this);
    }


    @Override
    public Variable maxSet2(VariableEquality left) {
        return this;
    }


    @Override
    public Variable maxSet2(VariableInterval left) {
        return new VariableInterval((VariableGreater) this.gt.maxSet2(left.gt),(VariableLess) this.lt.maxSet2(left.lt));
    }


    @Override
    public Variable maxSet2(VariableLess left) {
        return new VariableInterval(this.gt,(VariableLess) this.lt.maxSet2(left));        
    }


    @Override
    public Variable maxSet2(VariableGreater left) {
        return new VariableInterval((VariableGreater) this.gt.maxSet2(left),this.lt);
    }


    @Override
    public Variable maxSet2(VariableBoolean left) {
        throw new IllegalArgumentException();
    }


    @Override
    public RestrictionResult andTrue2(VariablePhantom left) {
        return new RestrictionResult(Variable.target(this, true, left.v, false));
    }


    @Override
    public Variable minSet2(VariablePhantom left) {
        return this;
    }


    @Override
    public Variable maxSet2(VariablePhantom left) {
        return this;
    }


    @Override
    public Variable target2(boolean trueL, VariablePhantom left) {
        return Variable.target(this, true, left.v, trueL);
    }
	
}
