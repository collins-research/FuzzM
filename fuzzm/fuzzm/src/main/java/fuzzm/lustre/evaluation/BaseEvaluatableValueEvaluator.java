/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.lustre.evaluation;

import fuzzm.value.hierarchy.EvaluatableValue;
import fuzzm.value.hierarchy.EvaluatableValueHierarchy;
import fuzzm.value.hierarchy.InstanceType;
import fuzzm.value.instance.BooleanInterval;
import fuzzm.value.instance.IntegerInterval;
import fuzzm.value.instance.RationalInterval;
import jkind.analysis.evaluation.Evaluator;
import jkind.lustre.BinaryExpr;
import jkind.lustre.BoolExpr;
import jkind.lustre.CastExpr;
import jkind.lustre.Expr;
import jkind.lustre.FunctionCallExpr;
import jkind.lustre.IfThenElseExpr;
import jkind.lustre.IntExpr;
import jkind.lustre.NamedType;
import jkind.lustre.RealExpr;
import jkind.lustre.UnaryExpr;
import jkind.lustre.values.Value;

public abstract class BaseEvaluatableValueEvaluator extends Evaluator {
	
	protected FunctionLookupEV fns;

	public BaseEvaluatableValueEvaluator(FunctionLookupEV fns) {
		this.fns = fns;
	}

	@Override
	public Value visit(BinaryExpr e) {
		//System.out.println(ID.location() + "BinaryExpr : " + e);
		Expr leftExpr = e.left;
		Expr rightExpr = e.right;
		EvaluatableValue leftValue = (EvaluatableValue) leftExpr.accept(this);
		EvaluatableValue rightValue = (EvaluatableValue) rightExpr.accept(this);			
		EvaluatableValue res = leftValue.applyBinaryOp(e.op,rightValue);
		//System.out.println(ID.location() + "((" + leftValue + ") " + e.op + " (" + rightValue + ")) := (" + res + ")");
		return res;
	}

	@Override
	public Value visit(UnaryExpr e) {
		//System.out.println("UnaryExpr : " + e);
		EvaluatableValue z = ((EvaluatableValue) e.expr.accept(this));
		EvaluatableValue res = z.applyUnaryOp(e.op);
		//if (Debug.isEnabled()) System.out.println(ID.location() + "(" + e.op + " (" + z + ")) := (" + res + ")");
		return res;
	}

	@Override
	public Value visit(IfThenElseExpr e) {
		Expr testExpr = e.cond;
		Expr thenExpr = e.thenExpr;
		Expr elseExpr = e.elseExpr;
		EvaluatableValue testValue = (EvaluatableValue) testExpr.accept(this);
		EvaluatableValue thenValue = (EvaluatableValue) thenExpr.accept(this);
		EvaluatableValue elseValue = (EvaluatableValue) elseExpr.accept(this);
		EvaluatableValue res = ((EvaluatableValueHierarchy)testValue).ite(thenValue,elseValue);
		//if (Debug.isEnabled()) System.out.println(ID.location() + "((" + testValue + ") ? (" + thenValue + ") : (" + elseValue + ")) := (" + res + ")");
		return res;
	}
	
	@Override
	public EvaluatableValue visit(CastExpr e) {
		EvaluatableValue res = (EvaluatableValue) e.expr.accept(this);
		return res.cast(e.type);
	}
	
	@Override
	abstract public EvaluatableValue visit(IntExpr e);

	@Override
	abstract public EvaluatableValue visit(RealExpr e);

	@Override
	abstract public EvaluatableValue visit(BoolExpr e);
	
	EvaluatableValue arbitraryValue(NamedType type) {
		if (type == NamedType.BOOL) return BooleanInterval.ARBITRARY;
		if (type == NamedType.INT)  return IntegerInterval.INFINITE_INTERVAL;
		if (type == NamedType.REAL) return RationalInterval.INFINITE_INTERVAL;
		throw new IllegalArgumentException();
	}
	
	@Override
	public EvaluatableValue visit(FunctionCallExpr e) {
		//System.out.println(ID.location() + "Evaluating : " + e);
		EvaluatableArgList args = new EvaluatableArgList();
		boolean all_instance_values = true;
		for (Expr v: e.args) {
			EvaluatableValue ev = (EvaluatableValue) v.accept(this);
			if (! (ev instanceof InstanceType<?>)) {
				all_instance_values = false;
				break;
			}
			args.add(ev);
		}
		return (all_instance_values) ? fns.get(e.function, args) : arbitraryValue(fns.getFnType(e.function));
	}
	
}
