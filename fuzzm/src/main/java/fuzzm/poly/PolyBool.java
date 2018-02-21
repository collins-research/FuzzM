package jfuzz.poly;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import jfuzz.lustre.evaluation.PolyFunctionMap;
import jfuzz.solver.SolverResults;
import jfuzz.util.Debug;
import jfuzz.util.ID;
import jfuzz.util.IntervalVector;
import jfuzz.util.ProofWriter;
import jfuzz.util.RatSignal;
import jfuzz.util.TypedName;
import jkind.util.BigFraction;

abstract public class PolyBool {

	public static final PolyBool TRUE  = new TruePolyBool(true,new VariableList());
	public static final PolyBool FALSE = new NotPolyBool(false,new VariableList());
	
	public boolean cex;
	final VariableList body;
	
	@Override
	abstract public String toString();
	
	abstract public String toACL2();
	
	protected PolyBool() {
		this.body = new VariableList();
		this.cex = true;
	}
	
	protected PolyBool(VariableList body) {
		this.body = body;
		this.cex = true;
		for (Variable v: body) {
			this.cex &= v.cex;
		}
	}
	
	protected PolyBool(boolean cex, VariableList body) {
		this.body = body;
		this.cex = cex;
	}
	
	protected PolyBool(Variable c) {
		this.body = new VariableList(c);
		this.cex = c.cex;
	}
	
	public static PolyBool less0(AbstractPoly arg) {
		//
		// We need to normalize these expressions immediately.
		//
		// Ax + poly < 0
		//if (Debug.isEnabled()) System.out.println(ID.location() + "less0 : (" + arg + ") < 0");
		if (arg.isConstant()) {
			return (arg.getConstant().signum() < 0) ? TRUE : FALSE;
		}
		boolean cex = arg.evaluateCEX().signum() < 0;
		VariableBound res = VariableBound.solvePolyLess0(arg, RelationType.EXCLUSIVE, FeatureType.FEATURE, cex);
		return new TruePolyBool(res);
	}
	
	public static PolyBool greater0(AbstractPoly arg) {
		//if (Debug.isEnabled()) System.out.println(ID.location() + "greater0 : (" + arg + ") > 0");
		// x + poly > 0
		if (arg.isConstant()) {
			return (arg.getConstant().signum() > 0) ? TRUE : FALSE;
		}
		boolean cex = arg.evaluateCEX().signum() > 0;
		VariableBound res = VariableBound.solvePolyGreater0(arg, RelationType.EXCLUSIVE, FeatureType.FEATURE, cex);
		return new TruePolyBool(res);
	}
	
	public static PolyBool equal0(AbstractPoly arg) {
		//System.out.println(ID.location() + "equal0(" + arg + ")");
		if (arg.isConstant()) {
			return (arg.getConstant().signum() == 0) ? TRUE : FALSE;
		}
		VariableID id = arg.leadingVariable();
		AbstractPoly  poly = arg.solveFor(id);
		// x = -poly
		VariableBound res = new VariableEquality(id,poly,arg.evaluateCEX().signum() == 0);
		return new TruePolyBool(res);		
	}
	
	private int features() {
		int res = 0;
		for (Variable vc: body) {
			res += vc.countFeatures();
		}
		return res;
	}

	private static PolyBool and_true(PolyBool x, PolyBool y) {
		VariableList xbody = x.isNegated() ? x.body.chooseAndNegateOne() : x.body;
		VariableList ybody = y.isNegated() ? y.body.chooseAndNegateOne() : y.body;
		PolyBool res = new TruePolyBool(true,VariableList.and(AndType.TRUE,xbody,ybody));
		if (Debug.logic()) {
			ProofWriter.printThms("and_true",x.toACL2(), y.toACL2(), res.toACL2());
		}
		return res;
	}
	
	private static PolyBool and_false(PolyBool x, PolyBool y) {
		if (Debug.logic()) 
			System.out.println(ID.location() + "andFalse: (" + x + " and "+ y + ")");		
		if ((! x.isNegated()) && (! y.isNegated())) {
			return new TruePolyBool(false,VariableList.and(AndType.FALSE,x.body,y.body));
		}
		if (x.features() > y.features()) {
			return x;
		}
		return y;
	}
	
	private static PolyBool and(PolyBool x, PolyBool y) {
	    //System.out.println(ID.location() + "x = " + x);
	    //System.out.println(ID.location() + "y = " + y);
        if (x.isTrue())  return y;
		if (y.isTrue())  return x;
		if (x.isFalse() || y.isFalse()) return PolyBool.FALSE;
		if (x.cex) {
			if (y.cex) {
				return and_true(x,y);
			} else {
				return y;
			}
		} else if (y.cex) {
			return x;
		} else {
			return and_false(x,y);
		}
	}
	
	protected abstract boolean isNegated();
	public abstract boolean isFalse();
	public abstract boolean isTrue();
	
	abstract public PolyBool not();	
	public PolyBool and(PolyBool arg) {
		PolyBool res = and(this,arg);
		if (Debug.isEnabled()) System.out.println(ID.location() + this.bytes() + " and " + arg.bytes() + " := " + res.bytes());
		return res;
	}
	
	public PolyBool or(PolyBool arg) {
		PolyBool res = and(this.not(),arg.not());
		res = res.not();
		if (Debug.isEnabled()) System.out.println(ID.location() + this.bytes() + " or " + arg.bytes() + " := " + res.bytes());
		return res;
	}
	
	public PolyBool iff(PolyBool value) {
	    // (iff a b) = (or (and a b) (and (not a) (not b)))
        PolyBool a = this;
        PolyBool b = value;
        PolyBool m1 = and(a,b);
        PolyBool m2 = and(a.not(),b.not());        
	    //System.out.println(ID.location() + "a = " + a);
	    //System.out.println(ID.location() + "b = " + b);
	    PolyBool res = m1.or(m2);
//	    if (a.cex && b.cex) {
//	        //System.out.println(ID.location() + "case 1: TT");
//	        res = and(a,b);
//	    } else if (!a.cex && !b.cex) {
//	        //System.out.println(ID.location() + "case 2: FF");
//	        a = a.not();
//	        b = b.not();
//            res = and(a,b);
//	    } else if (a.cex && !b.cex) {
//	        //System.out.println(ID.location() + "case 3: TF");
//            res = and(a,b.not()).not();
//	    } else {
//	        //System.out.println(ID.location() + "case 4: FT");
//            res = and(a.not(),b).not();
//	    }
		//System.out.println(ID.location() + "iff = " + res);
		return res;
	}

	public RatSignal randomVector(boolean biased, BigFraction min, BigFraction max, IntervalVector span, Map<VariableID,BigFraction> ctx) {
		return body.randomVector(biased, min, max, span, ctx);
	}
	
	public static PolyBool range(VariableID v, BigFraction min, BigFraction max) {
		PolyBase minP = new PolyBase(min);
		PolyBase maxP = new PolyBase(max);
		VariableGreater gt = new VariableGreater(v,v.cex.compareTo(min) >= 0,RelationType.INCLUSIVE,minP,FeatureType.FEATURE);
		VariableLess    lt = new VariableLess(v,v.cex.compareTo(max) <= 0,RelationType.INCLUSIVE,maxP,FeatureType.FEATURE);
		return new TruePolyBool(new VariableInterval(gt,lt,OpType.AND));
	}

	abstract public PolyBool normalize();

	public int bytes() {
		return body.size();
	}

	public Collection<VariableID> unboundVariables() {
		return body.unboundVariables();
	}

	public Map<TypedName,RegionBounds> intervalBounds() {
		Map<VariableID,RegionBounds> r1 = body.intervalBounds();
		Map<TypedName,RegionBounds> res = new HashMap<>();
		for (VariableID vid: r1.keySet()) {
			TypedName name = vid.name.name;
			if (! res.containsKey(name)) {
				res.put(name, r1.get(vid));
			} else {
				res.put(name, r1.get(vid).union(res.get(name)));
			}
		}
		return res;
	}

	abstract public SolverResults optimize(SolverResults cex, PolyFunctionMap fmap, RatSignal target);
	
}
