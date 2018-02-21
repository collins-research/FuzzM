package jfuzz.lustre.evaluation;

import java.util.List;

import jfuzz.poly.PolyBool;
import jfuzz.util.Debug;
import jfuzz.util.EvaluatableSignal;
import jfuzz.util.EvaluatableVector;
import jfuzz.util.ID;
import jfuzz.util.ProofWriter;
import jfuzz.util.StringMap;
import jfuzz.util.TypedName;
import jfuzz.value.hierarchy.EvaluatableValue;
import jfuzz.value.poly.BooleanPoly;
import jfuzz.value.poly.GlobalState;
import jfuzz.value.poly.PolyEvaluatableValue;
import jkind.lustre.BinaryExpr;
import jkind.lustre.BinaryOp;
import jkind.lustre.Equation;
import jkind.lustre.Expr;
import jkind.lustre.IdExpr;
import jkind.lustre.IfThenElseExpr;
import jkind.lustre.NamedType;
import jkind.lustre.Node;
import jkind.lustre.Program;
import jkind.lustre.Type;
import jkind.lustre.UnaryExpr;
import jkind.lustre.UnaryOp;
import jkind.lustre.builders.ProgramBuilder;
import jkind.lustre.values.Value;
import jkind.lustre.visitors.TypeReconstructor;
import jkind.util.Util;

public abstract class DepthFirstSimulator extends BaseEvaluatableValueEvaluator {
	
	//private final int k;
	protected final StringMap<Type> types;
	private final StringMap<Expr> equations = new StringMap<Expr>();
	private final List<Expr> assertions;
	private final TypeReconstructor tx;
	
	private int step = 0;
	private EvaluatableSignal state;
	private int thms = 0;
	
	protected DepthFirstSimulator(FunctionLookupEV fns, Node node) {
		super(fns);
		for (Equation eq : node.equations) {
			equations.put(((IdExpr) eq.lhs.get(0)).id,eq.expr);
		}
		assertions = node.assertions;
		types = new StringMap<Type>(Util.getTypeMap(node));
		ProgramBuilder pb = new ProgramBuilder();
		pb.addNode(node);
		Program prog = pb.build();
		tx = new TypeReconstructor(prog);
		tx.setNodeContext(node);
	}

	
	public PolyBool simulateProperty(EvaluatableSignal state, String property) {
		assert(step == 0);
		int k = state.size();
		System.out.println(ID.location() + "Counterexample Depth : " + k);
		this.state = new EvaluatableSignal(state);
		EvaluatableValue prop = BooleanPoly.TRUE;
		EvaluatableValue newprop;
		for (int time = 0; time < k; time++) {
			step = time;
			for (Expr asrt: assertions) {
				PolyEvaluatableValue asv = (PolyEvaluatableValue) eval(asrt);
				newprop = prop.and(asv);	
				if (Debug.logic()) {
					System.out.println(ID.location() + "Assertion " + asrt + " evaluated to " + asv + " [" + asv.cex() + "]");	
					System.out.println(ID.location() + "Accumulated Assertions [" + thms + "] " + newprop);
				}
				if (Debug.isEnabled()) { 
					System.out.println(ID.location() + "Assertion " + asrt + " evaluated to " + asv + " [" + asv.cex() + "]");
					String asvString = asv.toACL2();
					String preString = ((PolyEvaluatableValue) prop).toACL2();
					String postString = ((PolyEvaluatableValue) newprop).toACL2();
					ProofWriter.printThms(String.valueOf(thms),asvString,preString,postString);
					System.out.println(ID.location() + "Accumulated Assertions [" + thms + "] " + newprop);
					thms++;
				}
				prop = newprop;
				assert(step == time);
			}
		}
		step = k-1;
		Expr propExpr = equations.get(property);
		PolyEvaluatableValue propVal = (PolyEvaluatableValue) eval(propExpr);
		propVal = (PolyEvaluatableValue) propVal.not();
		newprop = prop.and(propVal);
		if (Debug.logic()) {
			System.out.println(ID.location() + "Property not(" + propExpr + ") evaluated to " + propVal + " [" + propVal.cex() + "]");
			System.out.println(ID.location() + "Final property [" + thms + "] " + newprop);
		}
		if (Debug.isEnabled()) {
			System.out.println(ID.location() + "Property not(" + propExpr + ") evaluated to " + propVal + " [" + propVal.cex() + "]");
			String propString = propVal.toACL2();
			String preString = ((PolyEvaluatableValue) prop).toACL2();
			String postString = ((PolyEvaluatableValue) newprop).toACL2();
			ProofWriter.printThms(String.valueOf(thms),propString,preString,postString);
			System.out.println(ID.location() + "Final property [" + thms + "] " + newprop);
			thms++;
		}
		prop = newprop;		
		PolyBool polyProp = ((BooleanPoly) prop).value;
		PolyBool invariants = GlobalState.getInvariants();
		PolyBool res = polyProp.and(invariants);
		if (Debug.logic()) {
			System.out.println(ID.location() + "Invariants : " + invariants);		
			System.out.println(ID.location() + "Final result [" + thms + "] " + res);
		}
		if (Debug.isEnabled()) {
			System.out.println(ID.location() + "Property   : " + polyProp);
			System.out.println(ID.location() + "Invariants : " + invariants);
			ProofWriter.printThms(String.valueOf(thms),polyProp.toACL2(),invariants.toACL2(),res.toACL2());
			System.out.println(ID.location() + "Final result [" + thms + "] " + res);
			thms++;
		}

		return res;
	}
	
	@Override
	public abstract Value visit(IfThenElseExpr e);
	
	@Override
	public Value visit(IdExpr e) {
		EvaluatableVector v = state.get(step);
		TypedName tname = new TypedName(e.id,(NamedType) types.get(e.id));
		if (v.containsKey(tname)) {
			PolyEvaluatableValue res = (PolyEvaluatableValue) v.get(tname);
			if (Debug.isEnabled()) System.out.println(ID.location() + e.id + " evaluated to " + res + " [" + res.cex() + "] in time step " + step);
			return res;
		}
		Expr expr = equations.get(e.id);
		if (expr == null) {
			System.out.println(ID.location() + "Warning: using default value for " + e);
			return getDefaultValue(e);
		}
		PolyEvaluatableValue value = (PolyEvaluatableValue) eval(expr);
		if (Debug.isEnabled()) System.out.println(ID.location() + e.id + " = " + expr + " evaluated to " + value + " [" + value.cex() + "] in time step " + step);
		state.set(new TypedName(e.id,(NamedType) types.get(e.id)),step,value);
		return value;
	}

	abstract protected Value getDefaultValue(IdExpr e);

	protected Type typeOf(Expr expr) {
		return expr.accept(tx);
	}
	
	@Override
	public Value visit(BinaryExpr e) {
		if (e.op == BinaryOp.ARROW) {
			if (step == 0) {
				return e.left.accept(this);
			} else {
				return e.right.accept(this);
			}
		} else {
			return super.visit(e);
		}
	}

	@Override
	public Value visit(UnaryExpr e) {
		if (e.op == UnaryOp.PRE) {
			assert(step > 0);
			step--;
			Value value = e.expr.accept(this);
			step++;
			return value;
		} else {
			return super.visit(e);
		}
	}

}
