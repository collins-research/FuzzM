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

import fuzzm.util.ID;
import fuzzm.util.Rat;
import fuzzm.value.instance.RationalInfinity;
import fuzzm.value.instance.RationalValue;
import jkind.lustre.BinaryOp;
import jkind.lustre.NamedType;
import jkind.util.BigFraction;

public class VariableGreater extends VariableInequality {

	protected VariableGreater(VariableID name, boolean cex, RelationType relation, AbstractPoly poly, FeatureType feature, TargetType target) {
		super(name,cex,relation,poly,feature,target);
		if (! ((relation == RelationType.EXCLUSIVE) ? cex == (name.cex.compareTo(poly.evaluateCEX()) > 0) : cex == (name.cex.compareTo(poly.evaluateCEX()) >= 0))) {
			System.out.println(ID.location() + this.toString());
			System.out.println(ID.location() + this.cexString());
			assert(false);
		};
	}
	
	protected VariableGreater(VariableID name, AbstractPoly poly, boolean cex, TargetType target) {
		this(name,cex,RelationType.EXCLUSIVE,poly,FeatureType.FEATURE,target);
	}

	protected VariableGreater(VariableID name, AbstractPoly poly, RelationType relation, boolean cex, TargetType target) {
		this(name,cex,relation,poly,FeatureType.FEATURE,target);
	}
//
//	protected VariableGreater(VariableID name, RelationType relation, AbstractPoly poly, FeatureType feature, boolean cex) {
//		this(name,OpType3.NEITHER,relation,poly,feature,cex,TerminalBool.ANY);
//	}
//
//	protected VariableGreater(VariableGreater source, VariableID name, RelationType relation, AbstractPoly poly, boolean cex) {
//		this(name,source.listOp,relation,poly,FeatureType.NONFEATURE,cex,source.context);
//	}
//	
//    public VariableGreater(VariableInequality source, boolean cex, RelationType relation) {
//		this(source.vid,cex,relation,source.poly,source.feature,source.target);
//	}
//	
	public VariableGreater(VariableGreater source, TargetType target) {
		this(source.vid,source.cex,source.relation,source.poly,source.feature,target);
	}
//	

//	@Override
//	public RationalType[] variableRange() {
//		RationalType range[] = polyRange();
//		return new RationalType[]{range[0],RationalInfinity.POSITIVE_INFINITY};
//	}

//	@Override
//	public VariableConstraint newConstraint(VariableID name, RelationType relation, AbstractPoly poly, boolean cex) {
//		return new VariableGreater(this,name,relation,poly,cex);
//	}
//
	@Override
	public String toACL2() {
		return toACL2(vid.cex.toString());
	}

    @Override
    public String toACL2(String cex) {
        return "(<" + ((relation == RelationType.INCLUSIVE) ? "= " : " ") + poly.toACL2() + vid.toACL2(cex) + ")";
    }

	@Override
	public String toString() {
		return poly + opString(VariableLocation.RIGHT,target.toString()) + vid + statusString() ;
	}

	@Override
	public String cexString() {
		return poly.cexString() + opString(VariableLocation.RIGHT,target.toString()) + vid.cex;
	}

	@Override
	protected String opString(VariableLocation location, String target) {
	    String inclusive = ((relation == RelationType.INCLUSIVE) ? "=" : "");
		return (location.equals(VariableLocation.LEFT) ?  " " + target + ">" + inclusive + " " : " " + "<" + inclusive + target + " ");
	}

	@Override
	protected String polyString() {
		return poly.toString();
	}

//	@Override
//	protected VariableConstraint newConstraint(BooleanContext context) {
//		return new VariableGreater(this,context);
//	}

	@Override
	public RestrictionResult andTrue(Variable x) {
		assert(cex && x.cex);
		RestrictionResult res = ((VariableInterface) x).andTrue2(this);
		//if (Debug.enabled) System.out.println(ID.location() + "(" + this.toString1() + ") and ("+ x.toString1() + ") := (" + res + ")");
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

	// ACL2: (def::trueAnd andTrue-variableGreater-variableLess (x y cex)
	@Override
	public RestrictionResult andTrue2(VariableLess left) {
		return new RestrictionResult(new VariableInterval(this,left));
	}

	// ACL2: (def::trueAnd andTrue-variableGreater-variableGreater (x y cex)
	@Override
	public RestrictionResult andTrue2(VariableGreater left) {
		return restrictInequality(left,this);
	}
	
	@Override
	protected RegionBounds constraintBounds(Map<VariableID, BigFraction> ctx) {
		RationalValue bound = new RationalValue(poly.evaluate(ctx));
		return new RegionBounds(bound,relation,RationalInfinity.POSITIVE_INFINITY,RelationType.INCLUSIVE);
	}

    @Override
    protected RegionBounds constraintBounds() {
        RationalValue bound = new RationalValue(poly.evaluateCEX());
        return new RegionBounds(bound,relation,RationalInfinity.POSITIVE_INFINITY,RelationType.INCLUSIVE);
    }

	@Override
	protected RegionBounds intervalBounds(Map<VariableID,RegionBounds> ctx) {
		RegionBounds x = poly.polyBounds(ctx);
		return new RegionBounds(x.lower,x.lowerType.inclusiveAND(this.relation),RelationType.INCLUSIVE,RationalInfinity.POSITIVE_INFINITY,RelationType.INCLUSIVE);
	}

	// ACL2: (def::un chooseBestComplement-variableGreater-variableInterval (x y)
	@Override
	public VariableInequality chooseBestCompliment(VariableInterval arg) {
		if (arg.gt.countFeatures() > arg.lt.countFeatures()) {
			return arg.gt;
		}
		return arg.lt;
	}

	@Override
	public RestrictionResult andTrue2(VariableBoolean left) {
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
			return new VariableGreater(vid, this.poly.add(BigFraction.ONE.divide(L)), RelationType.INCLUSIVE, cex, this.target);
		}
		BigInteger  G = this.poly.constantLCDContribution();
		L = L.divide(G);
		BigFraction C = this.poly.getConstant();
		AbstractPoly res = this.poly.subtract(C);
		C = Rat.roundUp(C.multiply(L));
		res = res.add(C.divide(L));
		return new VariableGreater(vid,res,RelationType.INCLUSIVE,cex,this.target);
	}

	@Override
	public boolean evalCEX(Map<VariableID, BigFraction> ctx) {
		BigFraction p = poly.evaluate(ctx);
		BigFraction x = ctx.get(this.vid);
		return (this.relation == RelationType.EXCLUSIVE) ? (x.compareTo(p) > 0) : (x.compareTo(p) >= 0);
	}

	@Override
	public VariableGreater rewrite(Map<VariableID, AbstractPoly> rewrite) {
		return new VariableGreater(vid, cex, relation, poly.rewrite(rewrite), feature, target);
	}

	@Override
	public AbstractPoly maxBound(int sign) {
		if (sign < 0) {
			return poly;
		}
		return new PolyBase(BigFraction.ZERO);
	}

    @Override
    public RestrictionResult mustContain(AbstractPoly v) {
        // poly <~ v
        // poly - v <~ 0
        AbstractPoly diff = poly.subtract(v);
        assert(diff.evaluateCEX().signum() < 0 || ((relation == RelationType.INCLUSIVE) && diff.evaluateCEX().signum() == 0));
        if (diff.isConstant()) {
            return new RestrictionResult(this);
        } else {
            VariableBound res = VariableBound.solvePolyLess0(diff, relation, cex, FeatureType.NONFEATURE, target);
            return new RestrictionResult(this,res);
        }
    }

    @Override
    public Variable target(boolean trueL, Variable right) {
        return right.target2(!trueL, this);
    }

    @Override
    public VariableGreater target2(boolean trueL, VariableInterval left) {
        return (VariableGreater) (trueL ? this.target2(trueL,left.gt) : Variable.target(this,true,left.lt,!trueL));
    }

    @Override
    public VariableGreater target2(boolean trueL, VariableEquality left) {
        if (trueL) return this;
        int cmp = this.poly.evaluateCEX().compareTo(left.poly.evaluateCEX());
        boolean target = (cmp > 0) || ((cmp == 0) && (this.relation == RelationType.EXCLUSIVE));
        return target ? new VariableGreater(this,TargetType.TARGET) : this;
    }

    @Override
    public VariableGreater target2(boolean trueL, VariableLess left) {
        if (trueL) return this;
        int cmp = this.poly.evaluateCEX().compareTo(left.poly.evaluateCEX());
        boolean target = (cmp > 0) || ((cmp == 0) && ((this.relation == RelationType.EXCLUSIVE) || (left.relation == RelationType.EXCLUSIVE)));
        return target ? new VariableGreater(this,TargetType.TARGET) : this;
    }

    @Override
    public VariableGreater target2(boolean trueL, VariableGreater left) {
        if (! trueL) return this;
        int cmp = this.poly.evaluateCEX().compareTo(left.poly.evaluateCEX());
        boolean target = (cmp > 0) || ((cmp == 0) && ((this.relation == RelationType.EXCLUSIVE) || (left.relation == RelationType.INCLUSIVE)));
        return target ? new VariableGreater(this,TargetType.TARGET) : this;
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
        return new VariableInterval((VariableGreater) this.minSet2(left.gt),left.lt);
    }

    @Override
    public Variable minSet2(VariableLess left) {
        return new VariableInterval(this,left);
    }

    @Override
    public Variable minSet2(VariableGreater left) {
        int cmp = left.poly.evaluateCEX().compareTo(this.poly.evaluateCEX());
        // Return the greater bound ..
        if ((cmp > 0) || ((cmp == 0) && this.relation == RelationType.INCLUSIVE)) {
            return left;
        }
        return this;
    }

    @Override
    public Variable minSet2(VariableBoolean left) {
        throw new IllegalArgumentException();
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
        return new VariableInterval((VariableGreater) this.maxSet2(left.gt),left.lt);
    }

    @Override
    public Variable maxSet2(VariableLess left) {
        return new VariableInterval(this,left);
    }

    @Override
    public Variable maxSet2(VariableGreater left) {
        int cmp = left.poly.evaluateCEX().compareTo(this.poly.evaluateCEX());
        if ((cmp > 0) || ((cmp == 0) && this.relation == RelationType.INCLUSIVE)) {
            return this;
        }
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
        return (isTarget() || target == TargetType.CHAFF) ? this : new VariableGreater(this,TargetType.TARGET);
    }

    @Override
    public BinaryOp binaryOp() {
        return (relation == RelationType.EXCLUSIVE) ? BinaryOp.GREATER : BinaryOp.GREATEREQUAL;
    }

}
