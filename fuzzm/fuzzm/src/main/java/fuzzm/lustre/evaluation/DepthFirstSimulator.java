/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.lustre.evaluation;

import java.util.List;

import fuzzm.poly.PolyBool;
import fuzzm.util.Debug;
import fuzzm.util.EvaluatableSignal;
import fuzzm.util.EvaluatableVector;
import fuzzm.util.ID;
import fuzzm.util.IDString;
import fuzzm.util.ProofWriter;
import fuzzm.util.StringMap;
import fuzzm.util.TypedName;
import fuzzm.value.hierarchy.EvaluatableValue;
import fuzzm.value.poly.BooleanPoly;
import fuzzm.value.poly.GlobalState;
import fuzzm.value.poly.PolyEvaluatableValue;
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
import jkind.lustre.values.Value;
import jkind.lustre.visitors.TypeReconstructor;
import jkind.util.Util;

public abstract class DepthFirstSimulator extends BaseEvaluatableValueEvaluator {
	
	//private final int k;
	protected final StringMap<Type> types;
	private final StringMap<Expr> equations = new StringMap<Expr>();
	private final List<Expr> assertions;
	private final TypeReconstructor tx;
	
	protected int step = 0;
	private EvaluatableSignal state;
	private int thms = 0;
	
	protected DepthFirstSimulator(FunctionLookupEV fns, Program prog) {
		super(fns);
		Node node = prog.getMainNode();
		for (Equation eq : node.equations) {
			equations.put(((IdExpr) eq.lhs.get(0)).id,eq.expr);
		}
		assertions = node.assertions;
		types = new StringMap<Type>(Util.getTypeMap(node));
		tx = new TypeReconstructor(prog);
		tx.setNodeContext(node);
	}

	
	public PolyBool simulateProperty(EvaluatableSignal state, String name, IDString property) {
		assert(step == 0);
		int k = state.size();
		System.out.println(ID.location() + "Counterexample Depth : " + k);
		this.state = new EvaluatableSignal(state);
		EvaluatableValue accumulatedAssertions = BooleanPoly.TRUE;
		EvaluatableValue nextAccumulator;
		for (int time = 0; time < k; time++) {
			step = time;
			for (Expr asrt: assertions) {
				PolyEvaluatableValue asv = (PolyEvaluatableValue) eval(asrt);
				assert(asv.cex().signum() != 0);
				nextAccumulator = accumulatedAssertions.and(asv);
				assert(((PolyEvaluatableValue) accumulatedAssertions).cex().signum() != 0);
				if (Debug.isEnabled()) { 
					System.out.println(ID.location() + "Assertion " + asrt + " evaluated to " + asv + " [" + asv.cex() + "]");
					System.out.println(ID.location() + "Accumulated Assertions [" + thms + "] " + nextAccumulator);
					String asvString = asv.toACL2();
					String preString = ((PolyEvaluatableValue) accumulatedAssertions).toACL2();
					String postString = ((PolyEvaluatableValue) nextAccumulator).toACL2();
					ProofWriter.printAndTT(ID.location(),String.valueOf(thms),asvString,preString,postString);
					System.out.println(ID.location() + "Accumulated Assertions [" + thms + "] " + nextAccumulator);
					thms++;
				}
				accumulatedAssertions = nextAccumulator;
				assert(step == time);
			}
		}
		step = k-1;
		Expr propExpr = equations.get(property.name());
		PolyEvaluatableValue propVal = (PolyEvaluatableValue) eval(propExpr);
		if (Debug.isEnabled()) 
		    System.out.println(ID.location() + name + " = " + propExpr + " evaluated to " + propVal + " [" + propVal.cex() + "]");
		PolyEvaluatableValue constraintVal = (PolyEvaluatableValue) propVal.not();
		assert(constraintVal.cex().signum() != 0);
		EvaluatableValue accumulatedConstraints = accumulatedAssertions.and(constraintVal);
		if (Debug.isEnabled()) {
			System.out.println(ID.location() + "Constraint not(" + propExpr + ") evaluated to " + constraintVal + " [" + constraintVal.cex() + "]");
			System.out.println(ID.location() + "Final Constraint [" + thms + "] " + accumulatedConstraints);
			String propString = constraintVal.toACL2();
			String preString = ((PolyEvaluatableValue) accumulatedAssertions).toACL2();
			String postString = ((PolyEvaluatableValue) accumulatedConstraints).toACL2();
			ProofWriter.printAndTT(ID.location(),String.valueOf(thms),propString,preString,postString);
			System.out.println(ID.location() + "Accumulated Constriant [" + thms + "] " + accumulatedConstraints);
			thms++;
		}	
		PolyBool polyConstraint = ((BooleanPoly) accumulatedConstraints).value;
		PolyBool globalInvariants = GlobalState.getInvariants();
		PolyBool finalConstraint = polyConstraint.and(globalInvariants);
		if (Debug.isEnabled()) {
		    System.err.println(ID.location() + "Accumulated Constraints : " + polyConstraint);
			System.err.println(ID.location() + "Global Invariants       : " + globalInvariants);
			ProofWriter.printAndTT(ID.location(),String.valueOf(thms),polyConstraint.toACL2(),globalInvariants.toACL2(),finalConstraint.toACL2());
			System.out.println(ID.location() + "Final Constraint [" + thms + "] " + finalConstraint);
			thms++;
		}

		return finalConstraint;
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
