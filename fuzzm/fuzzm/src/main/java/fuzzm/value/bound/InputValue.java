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

public class InputValue extends BoundValue {

	protected EvaluatableValue value;

	public InputValue(IndexedEvaluator evaluator, EvaluatableValue value, Type type, SortedSet<Integer> defSet, SortedSet<Integer> nextSet) {
		super(evaluator,type,defSet,nextSet);
		this.value = value;
	}

	@Override
	public EvaluatableValue getValue() {
		assert(value != null);
		return value;
	}

	@Override
	public int stepValue(Expr expr, ContainsEvaluatableValue[] preState, ContainsEvaluatableValue[] currState) {
		// Always changes
		return 1;
	}

	@Override
	public int initValue(Expr expr, ContainsEvaluatableValue[] binding) {
		// Always changes
		return 1;
	}

	@Override
	public boolean setValue(EvaluatableValue value) {
		assert(value != null);
		this.value = value;
		return true;
	}
	
}
