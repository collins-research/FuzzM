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

import fuzzm.util.BigIntegerEEA;
import fuzzm.util.Debug;
import fuzzm.util.ID;
import fuzzm.value.instance.RationalValue;
import jkind.lustre.BinaryOp;
import jkind.lustre.NamedType;
import jkind.util.BigFraction;

public class VariableEquality extends VariableRelation {

	protected VariableEquality(VariableID name, boolean cex, AbstractPoly poly, FeatureType feature, TargetType target) {
		super(name,cex,RelationType.INCLUSIVE,poly,feature,target);
		assert(cex == (name.cex.compareTo(poly.evaluateCEX()) == 0));
	}
	
	protected VariableEquality(VariableID name, AbstractPoly poly, boolean cex, TargetType target) {
		this(name,cex,poly,FeatureType.FEATURE,target);
	}
//	
//	protected VariableEquality(VariableEquality source, VariableID name, boolean cex, RelationType relation, AbstractPoly poly) {
//		// Use only for non-features ..
//		this(name,cex,relation,poly,FeatureType.NONFEATURE);
//	}
//
	protected VariableEquality(VariableEquality source, TargetType target) {
		this(source.vid,source.cex,source.poly,source.feature,target);
	}
	
//	protected VariableEquality(VariableEquality source) {
//		this(source.vid,context.listOp,source.relation,source.poly,source.feature,source.cex,context);
//	}
//
//	@Override
//	public int direction() {
//		return 0;
//	}
//
//	@Override
//	public VariableConstraint newConstraint(VariableID name, RelationType relation, AbstractPoly poly, boolean cex) {
//		return new VariableEquality(this,name,relation,poly,cex);
//	}
//	
//	@Override
//	protected VariableConstraint newConstraint(BooleanContext context) {
//		return new VariableEquality(this,context);
//	}

	@Override
	public String toACL2() {
		return toACL2(vid.cex.toString());
	}

    @Override
    public String toACL2(String cex) {
        return "(" + "= " + vid.toACL2(cex) + poly.toACL2() + ")";
    }

	@Override
	public String toString() {
		return vid + opString(VariableLocation.LEFT,target.toString()) + poly + statusString() ;
	}

	@Override
	public String cexString() {
		return vid.cex + "= " + poly.cexString();
	}

	@Override
	protected String opString(VariableLocation location, String target) {
		return " " + target + "= ";
	}

	@Override
	protected String polyString() {
		return poly.toString();
	}

	@Override
	public RestrictionResult andTrue(Variable x) {
		assert(cex && x.cex);
		return ((VariableInterface) x).andTrue2(this);
	}

//	// ACL2: (def::un linearizeTrue(x cex)
//	static VariableInequality linearizeTrue(VariableID v, VariableEquality eq) {
//		int sign = v.cex.compareTo(eq.poly.evaluateCEX());
//		if (sign < 0) {
//			return new VariableLess(v,eq.poly,eq.relation,true);
//		}
//		if (sign > 0) {
//			return new VariableGreater(v,eq.poly,eq.relation,true);
//		}
//		// sign == 0
//		return null;
//	}

	// ACL2: (def::un restrictEquality (x y)
	static RestrictionResult restrictEquality(VariableEquality x, VariableEquality y) {
		AbstractPoly diff = x.poly.subtract(y.poly);
		if (diff.isConstant()) return new RestrictionResult(x);
		VariableID vid = diff.leadingVariable();
		AbstractPoly sln = diff.solveFor(vid);
		VariableEquality res = new VariableEquality(vid,true,sln,x.feature,x.target.inherit(y.target));
		return new RestrictionResult(x,res);
	}	
	
	// ACL2: (def::trueAnd andTrue-variableEquality-variableLess (x y cex)
	@Override
	public RestrictionResult  andTrue2(VariableLess left) {		
	    RestrictionResult res = new RestrictionResult(this,VariableBound.restrictDisequality(this.poly, left.poly, left.relation, left.target.inherit(this.target)));
	    return res;
	}

	// ACL2: (def::trueAnd andTrue-variableEquality-variableGreater (x y cex)
	@Override
	public RestrictionResult  andTrue2(VariableGreater left) {
	    RestrictionResult res = new RestrictionResult(this,VariableBound.restrictDisequality(left.poly, this.poly, left.relation, left.target.inherit(this.target)));
	    return res;		
	}
	
	// ACL2: (def::trueAnd andTrue-variableEquality-variableInterval (x y cex)
	@Override
	public RestrictionResult  andTrue2(VariableInterval left) {			
	    List<Variable> list = VariableBound.restrictDisequality(this.poly,left.lt.poly,left.lt.relation, left.lt.target.inherit(this.target));
	    list.addAll(          VariableBound.restrictDisequality(left.gt.poly,this.poly,left.gt.relation, left.gt.target.inherit(this.target)));
	    RestrictionResult res = new RestrictionResult(this,list);
	    return res;					
	}

	// ACL2: (def::trueAnd andTrue-variableEquality-variableEquality (x y cex)
	@Override
	public RestrictionResult  andTrue2(VariableEquality left) {		
	    VariableEquality x;
	    VariableEquality y;
	    if (left.countFeatures() < this.countFeatures()) {
	        x = this;
	        y = left;
	    } else {
	        x = left;
	        y = this;
	    }
	    return restrictEquality(x,y);
	}

	@Override
	protected RegionBounds constraintBounds(Map<VariableID, BigFraction> ctx) {
		RationalValue value = new RationalValue(poly.evaluate(ctx));
		return new RegionBounds(value,RelationType.INCLUSIVE,relation,value,RelationType.INCLUSIVE);
	}

    @Override
    protected RegionBounds constraintBounds() {
        RationalValue value = new RationalValue(poly.evaluateCEX());
        return new RegionBounds(value,RelationType.INCLUSIVE,relation,value,RelationType.INCLUSIVE);
    }

	@Override
	protected RegionBounds intervalBounds(Map<VariableID,RegionBounds> ctx) {
		return poly.polyBounds(ctx);
	}

//	static VariableBound linearizeFalse(VariableID v, VariableEquality eq) {
//		int sign = v.cex.compareTo(eq.poly.evaluateCEX());
//		// System.out.println(ID.location() + v + "[" + v.cex + "] = " + eq.poly + "[" + eq.poly.evaluateCEX() + "]");
//        if (sign > 0) {
//			return new VariableGreater(v,eq.poly,eq.relation,true);
//		}
//		if (sign < 0) {
//			return new VariableLess(v,eq.poly,eq.relation,true);
//		}
//		throw new IllegalArgumentException();
//	}

	@Override
	public RestrictionResult andTrue2(VariableBoolean left) {
		// TODO Auto-generated method stub
		throw new IllegalArgumentException();
	}
	
	public static VariableEquality solveEquality(VariableID x, AbstractPoly poly, boolean cex, TargetType target) {
		AbstractPoly diff = poly.subtract(new PolyBase(x));
		VariableID vid = diff.leadingVariable();
		diff = diff.solveFor(vid);
		return new VariableEquality(vid,diff,cex,target);
	}
	
	public static AbstractPoly integerEqualityConstraint(AbstractPoly poly, TargetType target, List<Variable> res) {
		// gAx = gBy + Cz + D
		// gA(Bk)         = gB(Ak)
		// gA(iA(Cz+d)/g) = gB(-iB(Cz + D)/g) + (Cz + D)
		// 
		// gA(Bk + iA*(Cz + D)/g) = gB(Ak - iB(Cz + D)/g)) + (Cz + D)
		if (poly.isConstant()) return poly;
		BigInteger gA = poly.leastCommonDenominator();
		if (gA.compareTo(BigInteger.ONE) == 0) return poly;
// In some sense it feels like we are just doing this .. but I don't think that is quite true.
//		BigFraction cex = poly.evaluateCEX();
//		// We really do depend on k being "smaller" than .. whatever the current var is.
//		VariableID k = VariableID.alloc("z", NamedType.INT, cex);
//		Variable eq = solveEquality(k, poly, true);
//		res.add(eq);
//		AbstractPoly kpoly = new PolyBase(k);
//		return kpoly;
		AbstractPoly ipoly = poly.multiply(new BigFraction(gA));
		//System.out.println(ID.location() + "Constraining : " + gA + "(x) = " + ipoly);
		//System.out.println(ID.location() + "Constraining : " + A + "(x) = " + ipoly.cexString());
		VariableID yid = ipoly.leadingVariable();
		AbstractPoly reduced = ipoly.remove(yid);
		if (reduced.isConstant()) {
			BigFraction fgB = ipoly.getCoefficient(yid);
			// g *must* be equal to 1 .. right?
			assert(fgB.getDenominator().compareTo(BigInteger.ONE) == 0);
			VariableID k = yid.afterAlloc("eq", NamedType.INT, BigFraction.ZERO);
			//System.out.println(ID.location() + k + " allocated after " + yid);
			AbstractPoly y = new PolyBase(k).multiply(new BigFraction(gA)).add(yid.cex);
			//System.out.println(ID.location() + "Constraint   : " + yid + " = " + y);
			Variable eq = solveEquality(yid, y, true,target);
			res.add(eq);
			reduced = reduced.add(y.multiply(fgB));
			//System.out.println(ID.location() + "Updated Poly : " + gA + "(x) = " + reduced);
			reduced = reduced.divide(new BigFraction(gA));
			assert(reduced.evaluateCEX().compareTo(poly.evaluateCEX()) == 0);
			return reduced;
		} else {
			BigFraction fgB = ipoly.getCoefficient(yid);
			assert(fgB.getDenominator().compareTo(BigInteger.ONE) == 0);
			BigInteger gB = fgB.getNumerator();
			BigIntegerEEA eea = new BigIntegerEEA(gA,gB);
			BigInteger g = eea.gcd;
			BigInteger A = gA.divide(g);
			//BigInteger B = gB.divide(g);
			AbstractPoly inner = reduced.divide(new BigFraction(eea.gcd));
			inner = integerEqualityConstraint(inner,target,res);
			AbstractPoly y = inner.multiply(new BigFraction(eea.iB.negate()));
			BigFraction fkcex = yid.cex.subtract(y.evaluateCEX());
			assert(fkcex.getDenominator().compareTo(BigInteger.ONE) == 0);
			BigInteger  kcex = fkcex.getNumerator();
			assert(kcex.mod(A.abs()).compareTo(BigInteger.ZERO) == 0);
			kcex = kcex.divide(A);
			VariableID k = reduced.leadingVariable().afterAlloc("eq", NamedType.INT, new BigFraction(kcex));
			//System.out.println(ID.location() + k + " allocated after " + reduced.leadingVariable());
			y = y.add(new PolyBase(k).multiply(new BigFraction(A)));
//			System.out.println(ID.location());
//			System.out.println("Poly  : " + poly);
//			System.out.println("Poly  : " + poly.cexString());
//			System.out.println("gA    : " + gA);
//			System.out.println("iPoly : " + ipoly);
//			System.out.println("iPoly : " + ipoly.cexString());
//			System.out.println("yid   : " + yid);
//			System.out.println("yid   : " + yid.cex);
//			System.out.println("fgB   : " + fgB);
//			System.out.println("A     : " + A);
//			System.out.println("B     : " + B);			
//			System.out.println("inner : " + inner);
//			System.out.println("inner : " + inner.cexString());
//			System.out.println("-iB   : " + eea.iB.negate());
//			System.out.println("y     : " + y);
//			System.out.println("y     : " + y.cexString());
//			System.out.println("kcex  : " + kcex);
			assert(y.evaluateCEX().compareTo(yid.cex) == 0);
			//System.out.println(ID.location() + "Constraint   : " + yid + " = " + y);
			//System.out.println(ID.location() + "Constraint   : " + yid.cex + " = " + y.cexString());
			Variable eq = solveEquality(yid,y,true,target);
			res.add(eq);
			reduced = reduced.add(y.multiply(fgB));
			//System.out.println(ID.location() + "Updated Poly : " + gA + "(x) = " + reduced);
			reduced = reduced.divide(new BigFraction(gA));
			assert(reduced.evaluateCEX().compareTo(poly.evaluateCEX()) == 0);			
			return reduced;
		}
	}

	@Override
	public boolean requiresRestriction() {
		return cex && (this.relation == RelationType.INCLUSIVE) && (vid.name.name.type == NamedType.INT);
	}

	@Override
	public RestrictionResult restriction() {
		assert(requiresRestriction());
		List<Variable> res = new ArrayList<>();
		AbstractPoly poly = integerEqualityConstraint(this.poly,target,res);
		if (Debug.isEnabled()) {
			System.out.println(ID.location() + "Initial Equality  : " + this);
			System.out.println(ID.location() + "Initial Equality  : " + this.cexString());
			for (Variable v: res) {
				System.out.println(ID.location() + "Integer Contraint : " + v);	
				System.out.println(ID.location() + "Integer Contraint : " + v.cexString());	
			}
		}
		//System.out.println(ID.location() + "Pre Final Equality    : " + vid + " = " + poly);
		//System.out.println(ID.location() + "Pre Final Equality    : " + vid.cex + " = " + poly.cexString());
		VariableEquality ve = new VariableEquality(vid,poly,true,target);
		if (Debug.isEnabled()) {
			System.out.println(ID.location() + "Final Equality    : " + ve);
			System.out.println(ID.location() + "Final Equality    : " + ve.cexString());
		}
		return new RestrictionResult(ve,res);
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
	public boolean evalCEX(Map<VariableID, BigFraction> ctx) {
		BigFraction p = poly.evaluate(ctx);
		BigFraction x = ctx.get(this.vid);
		return (x.compareTo(p) == 0) ^ (this.relation == RelationType.EXCLUSIVE);
	}

	@Override
	public VariableEquality rewrite(Map<VariableID, AbstractPoly> rewrite) {
		return new VariableEquality(vid, cex, poly.rewrite(rewrite), feature,target);
	}

	@Override
	public AbstractPoly maxBound(int sign) {
		return new PolyBase(BigFraction.ZERO);
	}

    @Override
    public RestrictionResult mustContain(AbstractPoly v) {
        // v == poly
        // 0 == poly - v
        AbstractPoly diff = poly.subtract(v);
        assert(diff.evaluateCEX().signum() == 0);
        if (diff.isConstant()) {
            return new RestrictionResult(this);
        } else {
            VariableEquality res = VariableBound.solvePolyEquality0(diff, FeatureType.NONFEATURE, target);
            return new RestrictionResult(this,res);
        }
    }

    @Override
    public Variable target(boolean trueL, Variable right) {
        return right.target2(!trueL,this);
    }

    @Override
    public VariableEquality target2(boolean trueL, VariableInterval left) {
        VariableEquality z1 = (VariableEquality) this.target2(trueL,left.lt);
        if (z1.isTarget()) return z1;
        return this.target2(trueL,left.gt);
    }

    @Override
    public VariableEquality target2(boolean trueL, VariableEquality left) {
        int cmp = this.poly.evaluateCEX().compareTo(left.poly.evaluateCEX());
        return ((cmp == 0) == trueL) ? new VariableEquality(this,TargetType.TARGET) : this;
    }

    @Override
    public VariableEquality target2(boolean trueL, VariableLess left) {
        int cmp = this.poly.evaluateCEX().compareTo(left.poly.evaluateCEX());
        cmp = trueL ? cmp : (- cmp);
        RelationType rel = trueL ? left.relation : left.relation.not();
        boolean target = (cmp < 0) || (cmp == 0) && (rel == RelationType.INCLUSIVE);
        return target ? new VariableEquality(this,TargetType.TARGET) : this;
    }

    @Override
    public VariableEquality target2(boolean trueL, VariableGreater left) {
        int cmp = this.poly.evaluateCEX().compareTo(left.poly.evaluateCEX());
        cmp = trueL ? cmp : (- cmp);
        RelationType rel = trueL ? left.relation : left.relation.not();
        boolean target = (cmp > 0) || (cmp == 0) && (rel == RelationType.INCLUSIVE);
        return target ? new VariableEquality(this,TargetType.TARGET) : this;
    }

    @Override
    public Variable target2(boolean trueL, VariableBoolean left) {
        throw new IllegalArgumentException();
    }

    @Override
    public Variable minSet(Variable right) {
        return this;
    }

    @Override
    public Variable minSet2(VariableEquality left) {
        return this;
    }

    @Override
    public Variable minSet2(VariableInterval left) {
        return this;
    }

    @Override
    public Variable minSet2(VariableLess left) {
        return this;
    }

    @Override
    public Variable minSet2(VariableGreater left) {
        return this;
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

    @Override
    public VariableRelation setTarget(TargetType target) {
        return (isTarget() || target == TargetType.CHAFF) ? this : new VariableEquality(this,TargetType.TARGET);
    }

    @Override
    public BinaryOp binaryOp() {
        return BinaryOp.EQUAL;
    }


}
