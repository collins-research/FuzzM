/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.value.bound;

import java.util.SortedSet;

import fuzzm.lustre.evaluation.IndexedEvaluator;
import fuzzm.value.hierarchy.EvaluatableValue;
import jkind.lustre.Expr;
import jkind.lustre.Type;

public class ComputedValue extends InputValue {

	public ComputedValue(IndexedEvaluator evaluator, Type type, SortedSet<Integer> defSet, SortedSet<Integer> nextSet) {
		super(evaluator,null,type,defSet,nextSet);
	}

	@Override
	public boolean setValue(EvaluatableValue value) {
		assert(false);
		return false;
	}
	
	@Override
	public int stepValue(Expr expr, ContainsEvaluatableValue[] preState, ContainsEvaluatableValue[] currState) {
		evaluator.updatePreState(preState);
		evaluator.updateCurrState(currState);
		EvaluatableValue newValue = (EvaluatableValue) expr.accept(evaluator);
		EvaluatableValue oldValue = value;
		//System.out.println(ID.location() + oldValue + " |-> " + newValue);
		value = newValue;
		return (! newValue.equals(oldValue)) ? 1 : 0;
	}

	@Override
	public int initValue(Expr expr, ContainsEvaluatableValue[] preState) {
		//System.out.println(ID.location() + "initValue() Evaluating : " + expr);
		evaluator.updateCurrState(preState);
		evaluator.updatePreState(preState);
		//System.out.println(ID.location() + "initValue(" + expr + ")");
		EvaluatableValue newValue = (EvaluatableValue) expr.accept(evaluator.initExtendedEvaluator);
		EvaluatableValue oldValue = value;
		//System.out.println(ID.location() + oldValue + " |-> " + newValue);
		value = newValue;
		return (! newValue.equals(oldValue)) ? 1 : 0;
	}

}

