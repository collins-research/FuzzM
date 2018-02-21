package jfuzz.poly;

import java.math.BigInteger;
import java.util.Map;

import jfuzz.util.ID;
import jfuzz.util.Rat;
import jfuzz.value.instance.RationalInfinity;
import jfuzz.value.instance.RationalValue;
import jkind.lustre.NamedType;
import jkind.util.BigFraction;

public class VariableGreater extends VariableInequality {

	protected VariableGreater(VariableID name, boolean cex, RelationType relation, AbstractPoly poly, FeatureType feature) {
		super(name,cex,relation,poly,feature);
		if (! ((relation == RelationType.EXCLUSIVE) ? cex == (name.cex.compareTo(poly.evaluateCEX()) > 0) : cex == (name.cex.compareTo(poly.evaluateCEX()) >= 0))) {
			System.out.println(ID.location() + this.toString());
			System.out.println(ID.location() + this.cexString());
			assert(false);
		};
	}
	
	protected VariableGreater(VariableID name, AbstractPoly poly, boolean cex) {
		this(name,cex,RelationType.EXCLUSIVE,poly,FeatureType.FEATURE);
	}

	protected VariableGreater(VariableID name, AbstractPoly poly, RelationType relation, boolean cex) {
		this(name,cex,relation,poly,FeatureType.FEATURE);
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
    public VariableGreater(VariableInequality source, boolean cex, RelationType relation) {
		this(source.vid,cex,relation,source.poly,source.feature);
	}
//	
//	public VariableGreater(VariableBound source, BooleanContext context) {
//		this(source.name,context.listOp,source.relation,source.poly,source.feature,source.cex,context);
//	}
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
		return "(<" + ((relation == RelationType.INCLUSIVE) ? "= " : " ") + poly.toACL2() + "(id ," + vid + " " + vid.cex + "))";
	}

	@Override
	public String toString() {
		return poly + " <"  + ((relation == RelationType.INCLUSIVE) ? "= " : " ") + vid + statusString() ;
	}

	@Override
	public String cexString() {
		return poly.cexString() + " <"  + ((relation == RelationType.INCLUSIVE) ? "= " : " ") + vid.cex;
	}

	@Override
	protected String opString(VariableLocation location) {
		return (location.equals(VariableLocation.LEFT) ? " >" : " <") + ((relation == RelationType.INCLUSIVE) ? "= " : " ");
	}

	@Override
	protected String polyString() {
		return poly.toString();
	}

	@Override
	public VariableLess not() {
		return new VariableLess(this,! cex,relation.not());
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
		return new RestrictionResult(new VariableInterval(this,left,OpType.AND));
	}

	// ACL2: (def::trueAnd andTrue-variableGreater-variableGreater (x y cex)
	@Override
	public RestrictionResult andTrue2(VariableGreater left) {
		return restrictInequality(left,this);
	}
	
	@Override
	public Variable andFalse(Variable arg) {
		assert(!cex && !arg.cex);
		Variable res = ((VariableInterface) arg).andFalse2(this);
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
		Variable res = new VariableInterval(this,left,OpType.AND);
		System.out.println("GT.andFalse2(LT) = " + res);
		return res;
	}

	@Override
	public Variable andFalse2(VariableGreater left) {
		return better(this,left);
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
			return new VariableGreater(vid, this.poly.add(BigFraction.ONE.divide(L)), RelationType.INCLUSIVE, cex);
		}
		BigInteger  G = this.poly.constantLCDContribution();
		L = L.divide(G);
		BigFraction C = this.poly.getConstant();
		AbstractPoly res = this.poly.subtract(C);
		C = Rat.roundUp(C.multiply(L));
		res = res.add(C.divide(L));
		return new VariableGreater(vid,res,RelationType.INCLUSIVE,cex);
	}

	@Override
	public boolean evalCEX(Map<VariableID, BigFraction> ctx) {
		BigFraction p = poly.evaluate(ctx);
		BigFraction x = ctx.get(this.vid);
		return (this.relation == RelationType.EXCLUSIVE) ? (x.compareTo(p) > 0) : (x.compareTo(p) >= 0);
	}

	@Override
	public VariableGreater rewrite(Map<VariableID, AbstractPoly> rewrite) {
		return new VariableGreater(vid, cex, relation, poly.rewrite(rewrite), feature);
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
            VariableBound res = VariableBound.solvePolyLess0(diff, relation, FeatureType.NONFEATURE, cex);
            return new RestrictionResult(this,res);
        }
    }

}
