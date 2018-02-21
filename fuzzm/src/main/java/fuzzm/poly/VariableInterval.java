package jfuzz.poly;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import jfuzz.util.ID;
import jfuzz.util.Rat;
import jfuzz.value.instance.RationalValue;
import jkind.lustre.NamedType;
import jkind.util.BigFraction;

public class VariableInterval extends VariableBound {

	VariableGreater gt;
	VariableLess    lt;
	OpType op;
	
	protected VariableInterval(VariableGreater gt, VariableLess lt, OpType op) {
		super(gt.vid,op.op(gt.cex,lt.cex));
		assert(gt.vid.compareTo(lt.vid) == 0);
		this.gt = gt;
		this.lt = lt;
		this.op = op;
	}

	
	@Override
	public int countFeatures() {
		return gt.countFeatures() + lt.countFeatures();
	}

	@Override
	public String toACL2() {
		if (op == OpType.AND) {
			return "(and " + gt.toACL2() + " " + lt.toACL2() + ")";
		} else {
			return "(or " + gt.toACL2() + " " + lt.toACL2() + ")";
		}
	}

	@Override
	public String toString() {
		if (op == OpType.AND) {
			return gt.statusString() + gt.polyString() + gt.opString(VariableLocation.RIGHT) + vid + lt.opString(VariableLocation.LEFT) + lt.polyString() + lt.statusString();
		}
		return "(" + gt.statusString() + vid + gt.opString(VariableLocation.LEFT) + gt.polyString() + " || " + lt.polyString() + lt.opString(VariableLocation.RIGHT) + vid + lt.statusString() + ")";
	}

	@Override
	public String cexString() {
		String op = (this.op == OpType.AND) ? "&&" : "||";
		return "(" + gt.cexString() + op + lt.cexString() + ")";
	}

	@Override
	public VariableInterval not() {
		return new VariableInterval(lt.not(),gt.not(),op.not());
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
		if (left.op == OpType.OR) {
			if (right.op == OpType.OR) {
				VariableInequality lh = (VariableInequality) better(left.gt,left.lt);
				VariableInequality rh = (VariableInequality) better(right.gt,right.lt);
				return lh.andTrue(rh);
			} else {
				VariableInequality lh = (VariableInequality) better(left.gt,left.lt);
				return right.andTrue(lh);
			}
		}
		if (right.op == OpType.OR) {
			VariableInequality rh = (VariableInequality) better(right.gt,right.lt);
			return left.andTrue(rh);
		}
		RestrictionResult gt = restrictInequality(left.gt,right.gt);
		RestrictionResult lt = restrictInequality(left.lt,right.lt);
		return RestrictionResult.restrictionInterval(gt,lt);
	}

	// ACL2: (def::trueAnd andTrue-variableInterval-variableLess (x y cex)
	@Override
	public RestrictionResult andTrue2(VariableLess left) {
		if (op == OpType.OR) {
			VariableInequality x = left.chooseBestCompliment(this);
			return x.andTrue2(left);
		}
		RestrictionResult res = restrictInequality(left,lt);
		VariableLess less = (VariableLess) res.newConstraint;		
		return new RestrictionResult(new VariableInterval(gt,less,OpType.AND),res.restrictionList);
	}

	@Override
	// ACL2: (def::trueAnd andTrue-variableInterval-variableGreater (x y cex)
	public RestrictionResult andTrue2(VariableGreater left) {
		if (op == OpType.OR) {
			VariableInequality x = left.chooseBestCompliment(this);
			return x.andTrue2(left);
		}
		RestrictionResult res = restrictInequality(left,gt);
		VariableGreater greater = (VariableGreater) res.newConstraint;	
		return new RestrictionResult(new VariableInterval(greater,lt,OpType.AND),res.restrictionList);
	}

	@Override
	public Variable andFalse(Variable x) {
		assert(!x.cex && this.cex);
		return ((VariableInterface) x).andFalse2(this);		
	}


	@Override
	public Variable andFalse2(VariableEquality left) {
		return left.andFalse2(this);
	}

	@Override
	public Variable andFalse2(VariableInterval left) {
		if (op == OpType.OR) {
			return better(this,left);
		}
		if (left.op == OpType.OR) {
			return better(this,left);
		}
		VariableLess    lt = (VariableLess) better(this.lt,left.lt);
		VariableGreater gt = (VariableGreater) better(this.gt,left.gt);
		return new VariableInterval(gt,lt,OpType.AND);
	}


	@Override
	public Variable andFalse2(VariableLess left) {
		if (op == OpType.OR) {
			return better(this,left);
		}
		VariableLess lt = (VariableLess) better(this.lt,left);
		return new VariableInterval(this.gt,lt,OpType.AND);
	}


	@Override
	public Variable andFalse2(VariableGreater left) {
		if (op == OpType.OR) {
			return better(this,left);
		}
		VariableGreater gt = (VariableGreater) better(this.gt,left);
		return new VariableInterval(gt,this.lt,OpType.AND);
		
	}

	@Override
	public boolean requiresRestriction() {
		AbstractPoly diff = lt.poly.subtract(gt.poly);
		return ! diff.isConstant();
	}

	@Override
	public RestrictionResult restriction() {
		AbstractPoly diff = lt.poly.subtract(gt.poly);
		return new RestrictionResult(this,VariableBound.solvePolyGreater0(diff, RelationType.INCLUSIVE,FeatureType.NONFEATURE,true));
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
	public Variable andFalse2(VariableBoolean left) {
		throw new IllegalArgumentException();
	}


	@Override
	public boolean implicitEquality() {
		AbstractPoly diff = lt.poly.subtract(gt.poly);
		if (diff.isConstant()) {
			BigFraction delta = diff.getConstant();
			if (delta.signum() == 0) {
				if (op == OpType.AND) {
					return (gt.relation == RelationType.INCLUSIVE) && (lt.relation == RelationType.INCLUSIVE);
				} else {
					return (gt.relation == RelationType.EXCLUSIVE) && (lt.relation == RelationType.EXCLUSIVE);
				}
			} else if (vid.name.name.type == NamedType.INT) {
				if (delta.compareTo(BigFraction.ONE) < 0) {
					AbstractPoly base = gt.poly.subtract(gt.poly.getConstant());
					BigInteger z = base.leastCommonDenominator();
					if (z.compareTo(BigInteger.ONE) == 0) {
						return (op == OpType.AND) && (delta.compareTo(BigFraction.ONE) < 0);
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
		if (delta.signum() == 0) {
			if (op == OpType.AND) {
				return new VariableEquality(vid,cex,RelationType.INCLUSIVE,gt.poly,gt.feature == lt.feature ? gt.feature : FeatureType.NONFEATURE);
			} else {
				return new VariableEquality(vid,cex,RelationType.EXCLUSIVE,gt.poly,gt.feature == lt.feature ? gt.feature : FeatureType.NONFEATURE);
			}
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
			return new VariableEquality(vid,cex,RelationType.INCLUSIVE,base,gt.feature == lt.feature ? gt.feature : FeatureType.NONFEATURE);
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
		return new VariableInterval(gt,lt,this.op);
	}

	@Override
	public boolean evalCEX(Map<VariableID, BigFraction> ctx) {
		return (this.op == OpType.AND) ? gt.evalCEX(ctx) & lt.evalCEX(ctx) : gt.evalCEX(ctx) & lt.evalCEX(ctx);
	}


	@Override
	public boolean reducableIntegerInterval() {
		if (lt.relation == RelationType.EXCLUSIVE || gt.relation == RelationType.EXCLUSIVE) return false;
		boolean integerInterval = (this.op == OpType.AND) && (vid.name.name.type == NamedType.INT) && !lt.poly.isConstant() && !gt.poly.isConstant();
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
			VariableGreater deltaBound = new VariableGreater(delta, true, RelationType.INCLUSIVE, new PolyBase(BigFraction.ZERO), lt.feature);
			List<Variable> restrictions = new ArrayList<>();
			eqpoly = VariableEquality.integerEqualityConstraint(eqpoly,restrictions);
			assert(eqpoly.evaluateCEX().compareTo(vid.cex) == 0);
			VariableEquality newBound = new VariableEquality(vid,true,RelationType.INCLUSIVE,eqpoly,lt.feature);
			// gt.poly <= xeq
			AbstractPoly gtpoly = gt.poly.subtract(eqpoly);
			VariableBound newGT = VariableBound.solvePolyLess0(gtpoly, RelationType.INCLUSIVE, gt.feature, true);
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
			VariableGreater deltaBound = new VariableGreater(delta, true, RelationType.INCLUSIVE, new PolyBase(BigFraction.ZERO), gt.feature);
			List<Variable> restrictions = new ArrayList<>();
			eqpoly = VariableEquality.integerEqualityConstraint(eqpoly,restrictions);
			assert(eqpoly.evaluateCEX().compareTo(vid.cex) == 0);
			VariableEquality newBound = new VariableEquality(vid,true,RelationType.INCLUSIVE,eqpoly,gt.feature);
			// xeq <= lt.poly
			AbstractPoly ltpoly = eqpoly.subtract(lt.poly);
			VariableBound newLT = VariableBound.solvePolyLess0(ltpoly, RelationType.INCLUSIVE, lt.feature, true);
			restrictions.add(newLT);
			restrictions.add(deltaBound);
			return new RestrictionResult(newBound,restrictions);			
		}
	}


	@Override
	public VariableInterval rewrite(Map<VariableID, AbstractPoly> rewrite) {
		return new VariableInterval(gt.rewrite(rewrite),lt.rewrite(rewrite),op);
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

	
}
