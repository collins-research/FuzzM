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
import java.util.Map;

import fuzzm.util.Rat;
import fuzzm.value.instance.RationalInfinity;
import fuzzm.value.instance.RationalValue;
import jkind.lustre.NamedType;
import jkind.util.BigFraction;

public class VariableLess extends VariableInequality {

	protected VariableLess(VariableID name, boolean cex, RelationType relation, AbstractPoly poly, FeatureType feature) {
		super(name,cex,relation,poly,feature);
		assert((relation == RelationType.EXCLUSIVE) ? cex == (name.cex.compareTo(poly.evaluateCEX()) < 0) : cex == (name.cex.compareTo(poly.evaluateCEX()) <= 0));
	}
	
	protected VariableLess(VariableID name, AbstractPoly poly, boolean cex) {
		this(name,cex,RelationType.EXCLUSIVE,poly,FeatureType.FEATURE);
	}
	
	protected VariableLess(VariableID name, AbstractPoly poly, RelationType relation, boolean cex) {
		this(name,cex,relation,poly,FeatureType.FEATURE);
	}
//
//	protected VariableLess(VariableID name, RelationType relation, AbstractPoly poly, FeatureType feature, boolean cex) {
//		this(name,OpType3.NEITHER,relation,poly,feature,cex,TerminalBool.ANY);
//	}
//
//	protected VariableLess(VariableLess source, VariableID name, RelationType relation, AbstractPoly poly, boolean cex) {
//		this(name,source.listOp,relation,poly,FeatureType.NONFEATURE,cex,source.context);
//	}
//	
	public VariableLess(VariableInequality source, boolean cex, RelationType relation) {
		this(source.vid,cex,relation,source.poly,source.feature);
	}
//	
//	public VariableLess(VariableBound source, BooleanContext context) {
//		this(source.name,context.listOp,source.relation,source.poly,source.feature,source.cex,context);
//	}
	
//	// conjoin()
//	@Override
//	public VariableConstraint newConstraint(VariableID name, RelationType relation, AbstractPoly poly, boolean cex) {
//		return new VariableLess(this,name,relation,poly,cex);
//	}
	
//	// cons()
//	@Override
//	protected VariableConstraint newConstraint(BooleanContext context) {
//		return new VariableLess(this,context);
//	}

	@Override
	public String toACL2() {
		return "(<" + ((relation == RelationType.INCLUSIVE) ? "= " : " ") + "(id ," + vid + " " + vid.cex + ")" + poly.toACL2() + ")";
	}

	@Override
	public String toString() {
		return vid + " <" + ((relation == RelationType.INCLUSIVE) ? "= " : " ") + poly + statusString();
	}

	@Override
	public String cexString() {
		return vid.cex + " <" + ((relation == RelationType.INCLUSIVE) ? "= " : " ") + poly.cexString();
	}

	@Override
	protected String opString(VariableLocation location) {
		return (location.equals(VariableLocation.LEFT) ? " <" : " >") + ((relation == RelationType.INCLUSIVE) ? "= " : " ");
	}

	@Override
	protected String polyString() {
		return poly.toString();
	}

	@Override
	public VariableGreater not() {
		return new VariableGreater(this,! cex,relation.not());
	}

	@Override
	public RestrictionResult andTrue(Variable x) {
		assert(cex && x.cex);
		RestrictionResult res = ((VariableInterface) x).andTrue2(this);
		return res;
	}

	@Override
	public RestrictionResult andTrue2(VariableEquality left) {
		return left.andTrue2(this);
	}

	@Override
	public RestrictionResult andTrue2(VariableInterval left) {
		return left.andTrue2(this);
	}

	// ACL2: (def::trueAnd andTrue-variableLess-variableLess (x y cex)
	@Override
	public RestrictionResult andTrue2(VariableLess left) {
		VariableLess p1 = left;
		VariableLess p2 = this;
		return restrictInequality(p1,p2);
	}

	// ACL2: (def::trueAnd andTrue-variableGreater-variableLess (x y cex)
	@Override
	public RestrictionResult andTrue2(VariableGreater left) {
		return new RestrictionResult(new VariableInterval(left,this,OpType.AND));
	}

	// ACL2: (def::un chooseBestComplement-variabeLess-variableInterval (x y)
	@Override
	public VariableInequality chooseBestCompliment(VariableInterval arg) {
		if (arg.lt.countFeatures() > arg.gt.countFeatures()) {
			return arg.lt;
		}
		return arg.gt;
	}
	
	@Override
	protected RegionBounds constraintBounds(Map<VariableID, BigFraction> ctx) {
		RationalValue bound = new RationalValue(poly.evaluate(ctx));
		return new RegionBounds(RationalInfinity.NEGATIVE_INFINITY,RelationType.INCLUSIVE,bound,relation);
	}

    @Override
    protected RegionBounds constraintBounds() {
        RationalValue bound = new RationalValue(poly.evaluateCEX());
        return new RegionBounds(RationalInfinity.NEGATIVE_INFINITY,RelationType.INCLUSIVE,bound,relation);
    }

	@Override
	protected RegionBounds intervalBounds(Map<VariableID,RegionBounds> ctx) {
		RegionBounds x = poly.polyBounds(ctx);
		return new RegionBounds(RationalInfinity.NEGATIVE_INFINITY,RelationType.INCLUSIVE,RelationType.INCLUSIVE,x.upper,x.upperType.inclusiveAND(this.relation));
	}

	@Override
	public Variable andFalse(Variable x) {
		System.out.println("LT.andFalse2(?)");
		assert(!cex && !x.cex);
		Variable res = ((VariableInterface) x).andFalse2(this);
		return res;
	}

	@Override
	public Variable andFalse2(VariableEquality left) {
		return left.andFalse2(this);
	}

	@Override
	public Variable andFalse2(VariableInterval left) {
		return left.andFalse2(this);
	}

	@Override
	public Variable andFalse2(VariableLess left) {
		return better(this,left);
	}

	@Override
	public Variable andFalse2(VariableGreater left) {
		return new VariableInterval(left,this,OpType.AND);
	}

	@Override
	public RestrictionResult andTrue2(VariableBoolean left) {
		// TODO Auto-generated method stub
		throw new IllegalArgumentException();
	}

	@Override
	public Variable andFalse2(VariableBoolean left) {
		// TODO Auto-generated method stub
		throw new IllegalArgumentException();
	}

	@Override
	public boolean slackIntegerBounds() {
		if (this.vid.name.name.type != NamedType.INT) return false;
		return ((this.relation == RelationType.EXCLUSIVE) || (this.poly.constantLCDContribution().compareTo(BigInteger.ONE) != 0));
	}

	@Override
	public Variable tightenIntegerBounds() {
		assert(slackIntegerBounds());
		BigInteger  L = this.poly.leastCommonDenominator();
		if ((this.relation == RelationType.EXCLUSIVE) && (this.poly.constantLCDContribution().compareTo(BigInteger.ONE) == 0)) {
			return new VariableLess(vid, this.poly.subtract(BigFraction.ONE.divide(L)), RelationType.INCLUSIVE, cex);
		}
		BigInteger  G = this.poly.constantLCDContribution();
		L = L.divide(G);
		BigFraction C = this.poly.getConstant();
		AbstractPoly res = this.poly.subtract(C);
		C = Rat.roundDown(C.multiply(L));
		res = res.add(C.divide(L));
		return new VariableLess(vid,res,RelationType.INCLUSIVE,cex);
	}

	@Override
	public boolean evalCEX(Map<VariableID, BigFraction> ctx) {
		BigFraction p = poly.evaluate(ctx);
		BigFraction x = ctx.get(this.vid);
		return (this.relation == RelationType.EXCLUSIVE) ? (x.compareTo(p) < 0) : (x.compareTo(p) <= 0);
	}

	@Override
	public VariableLess rewrite(Map<VariableID, AbstractPoly> rewrite) {
		return new VariableLess(vid, cex, relation, poly.rewrite(rewrite), feature);
	}
	
	@Override
	public AbstractPoly maxBound(int sign) {
		if (sign > 0) {
			return poly.negate();
		}
		return new PolyBase(BigFraction.ZERO);
	}

    @Override
    public RestrictionResult mustContain(AbstractPoly v) {
        // v <~ poly 
        // 0 <~ poly - v
        AbstractPoly diff = poly.subtract(v);
        assert(0 < diff.evaluateCEX().signum() || ((relation == RelationType.INCLUSIVE) && diff.evaluateCEX().signum() == 0));
        if (diff.isConstant()) {
            return new RestrictionResult(this);
        } else {
            VariableBound res = VariableBound.solvePolyGreater0(diff, relation, FeatureType.NONFEATURE, cex);
            return new RestrictionResult(this,res);
        }
    }

}
