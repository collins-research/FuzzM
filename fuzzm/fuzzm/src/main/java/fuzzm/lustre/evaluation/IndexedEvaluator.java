/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.lustre.evaluation;

import java.util.SortedSet;

import fuzzm.lustre.indexed.IndexedIdExpr;
import fuzzm.value.bound.ComputedValue;
import fuzzm.value.bound.ConstrainedValue;
import fuzzm.value.bound.ContainsEvaluatableValue;
import fuzzm.value.bound.InputValue;
import fuzzm.value.hierarchy.EvaluatableValue;
import jkind.lustre.IdExpr;
import jkind.lustre.Type;
import jkind.lustre.values.Value;

public abstract class IndexedEvaluator extends EvaluatableValueEvaluator {

	private ContainsEvaluatableValue currState[];
	
	public IndexedEvaluator(FunctionLookupEV fns) {
		super(fns);
		initExtendedEvaluator = new InitIndexedEvaluator(this);
	}

	@Override
	public Value visit(IdExpr e) {
		//System.out.println(ID.location() + e + " index: " + ((IndexedIdExpr) e).index);
		Value res = currState[((IndexedIdExpr) e).index].getValue();
		assert(res != null);
		return res;
	}

	public void updateCurrState(ContainsEvaluatableValue currState[]) {
		this.currState = currState;
	}
	
	public void updatePreState(ContainsEvaluatableValue preState[]) {
		((InitIndexedEvaluator) this.initExtendedEvaluator).preState = preState;
	}
	
	public InputValue inputValue(EvaluatableValue value, Type type, SortedSet<Integer> defSet, SortedSet<Integer> nextSet) {
		return new InputValue(this,value,type,defSet,nextSet);
	}
	
	public ComputedValue computedValue(Type type, SortedSet<Integer> defSet, SortedSet<Integer> nextSet) {
		return new ComputedValue(this,type,defSet,nextSet);		
	}
	
	public ConstrainedValue constrainedValue(boolean polarity) {
		return new ConstrainedValue(polarity,this);
	}
	
	abstract public EvaluatableValue trueValue();
	abstract public EvaluatableValue falseValue();
	
}
