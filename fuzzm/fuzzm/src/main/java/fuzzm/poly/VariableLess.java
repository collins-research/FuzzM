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
import jkind.lustre.BinaryOp;
import jkind.lustre.NamedType;
import jkind.util.BigFraction;

public class VariableLess extends VariableInequality {

	protected VariableLess(VariableID name, boolean cex, RelationType relation, AbstractPoly poly, FeatureType feature, TargetType target) {
		super(name,cex,relation,poly,feature,target);
		assert((relation == RelationType.EXCLUSIVE) ? cex == (name.cex.compareTo(poly.evaluateCEX()) < 0) : cex == (name.cex.compareTo(poly.evaluateCEX()) <= 0));
	}
	
	protected VariableLess(VariableID name, AbstractPoly poly, boolean cex, TargetType target) {
		this(name,cex,RelationType.EXCLUSIVE,poly,FeatureType.FEATURE,target);
	}
	
	protected VariableLess(VariableID name, AbstractPoly poly, RelationType relation, boolean cex, TargetType target) {
		this(name,cex,relation,poly,FeatureType.FEATURE,target);
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
//	public VariableLess(VariableInequality source, boolean cex, RelationType relation) {
//		this(source.vid,cex,relation,source.poly,source.feature);
//	}
//	
	public VariableLess(VariableLess source, TargetType target) {
	    this(source.vid,source.cex,source.relation,source.poly,source.feature,target);
	}

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
		return toACL2(vid.cex.toString());
	}

    @Override
    public String toACL2(String cex) {
        return "(<" + ((relation == RelationType.INCLUSIVE) ? "= " : " ") + vid.toACL2(cex) + poly.toACL2() + ")";
    }

	@Override
	public String toString() {
		return vid + opString(VariableLocation.LEFT,target.toString()) + poly + statusString();
	}

	@Override
	public String cexString() {
		return vid.cex + opString(VariableLocation.LEFT,target.toString()) + poly.cexString();
	}

    @Override
    protected String opString(VariableLocation location, String target) {
        String inclusive = ((relation == RelationType.INCLUSIVE) ? "=" : "");
        return (location.equals(VariableLocation.LEFT) ? " " + target + "<" + inclusive + " " : " " + inclusive + ">" + target + " ");
    }

	@Override
	protected String polyString() {
		return poly.toString();
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
		return new RestrictionResult(new VariableInterval(left,this));
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
			return new VariableLess(vid, this.poly.subtract(BigFraction.ONE.divide(L)), RelationType.INCLUSIVE, cex, target);
		}
		BigInteger  G = this.poly.constantLCDContribution();
		L = L.divide(G);
		BigFraction C = this.poly.getConstant();
		AbstractPoly res = this.poly.subtract(C);
		C = Rat.roundDown(C.multiply(L));
		res = res.add(C.divide(L));
		return new VariableLess(vid,res,RelationType.INCLUSIVE,cex, target);
	}

	@Override
	public boolean evalCEX(Map<VariableID, BigFraction> ctx) {
		BigFraction p = poly.evaluate(ctx);
		BigFraction x = ctx.get(this.vid);
		return (this.relation == RelationType.EXCLUSIVE) ? (x.compareTo(p) < 0) : (x.compareTo(p) <= 0);
	}

	@Override
	public VariableLess rewrite(Map<VariableID, AbstractPoly> rewrite) {
		return new VariableLess(vid, cex, relation, poly.rewrite(rewrite), feature, target);
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
            VariableBound res = VariableBound.solvePolyGreater0(diff, relation, cex, FeatureType.NONFEATURE, target);
            return new RestrictionResult(this,res);
        }
    }
    
    @Override
    public Variable target(boolean trueL, Variable right) {
        return right.target2(!trueL, this);
    }

    @Override
    public VariableLess target2(boolean trueL, VariableInterval left) {
        return (VariableLess) (trueL ? this.target2(trueL,left.lt) : Variable.target(this,true,left.gt,!trueL));
    }

    @Override
    public VariableLess target2(boolean trueL, VariableEquality left) {
        if (trueL) return this;
        int cmp = this.poly.evaluateCEX().compareTo(left.poly.evaluateCEX());
        boolean target = (cmp < 0) || ((cmp == 0) && (this.relation == RelationType.EXCLUSIVE));
        return target ? new VariableLess(this,TargetType.TARGET) : this;
    }

    @Override
    public VariableLess target2(boolean trueL, VariableGreater left) {
        if (trueL) return this;
        int cmp = this.poly.evaluateCEX().compareTo(left.poly.evaluateCEX());
        boolean target = (cmp < 0) || ((cmp == 0) && ((this.relation == RelationType.EXCLUSIVE) || (left.relation == RelationType.EXCLUSIVE)));
        return target ? new VariableLess(this,TargetType.TARGET) : this;
    }

    @Override
    public VariableLess target2(boolean trueL, VariableLess left) {
        if (! trueL) return this;
        int cmp = this.poly.evaluateCEX().compareTo(left.poly.evaluateCEX());
        boolean target = (cmp < 0) || ((cmp == 0) && ((this.relation == RelationType.EXCLUSIVE) || (left.relation == RelationType.INCLUSIVE)));
        return target ? new VariableLess(this,TargetType.TARGET) : this;
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
        return new VariableInterval(left.gt,(VariableLess) this.minSet2(left.lt));
    }

    @Override
    public Variable minSet2(VariableLess left) {
        int cmp = left.poly.evaluateCEX().compareTo(this.poly.evaluateCEX());
        // Return the smallest bound ..
        if ((cmp < 0) || ((cmp == 0) && this.relation == RelationType.INCLUSIVE)) {
            return left;
        }
        return this;
    }

    @Override
    public Variable minSet2(VariableGreater left) {
        return new VariableInterval(left,this);
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
        return new VariableInterval(left.gt,(VariableLess) this.maxSet2(left.lt));
    }

    @Override
    public Variable maxSet2(VariableLess left) {
        int cmp = left.poly.evaluateCEX().compareTo(this.poly.evaluateCEX());
        if ((cmp < 0) || ((cmp == 0) && this.relation == RelationType.INCLUSIVE)) {
            return this;
        }
        return left;
    }

    @Override
    public Variable maxSet2(VariableGreater left) {
        return new VariableInterval(left,this);
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
        return (isTarget() || target == TargetType.CHAFF) ? this : new VariableLess(this,TargetType.TARGET);
    }

    @Override
    public BinaryOp binaryOp() {
        return (relation == RelationType.EXCLUSIVE) ? BinaryOp.LESS : BinaryOp.LESSEQUAL;
    }

}
