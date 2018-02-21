package jfuzz.value.bound;

import java.util.SortedSet;

import jfuzz.lustre.evaluation.IndexedEvaluator;
import jfuzz.value.hierarchy.EvaluatableValue;
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
		// DAG - is this right?
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

