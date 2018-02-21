package jfuzz.value.bound;

import java.util.TreeSet;

import jfuzz.lustre.evaluation.IndexedEvaluator;
import jfuzz.value.hierarchy.BooleanTypeInterface;
import jfuzz.value.hierarchy.EvaluatableValue;
import jkind.lustre.Expr;
import jkind.lustre.NamedType;

public class ConstrainedValue extends BoundValue {

	private boolean polarity;
	EvaluatableValue value;
	
	public ConstrainedValue(boolean polarity, IndexedEvaluator evaluator) {
		super(evaluator,NamedType.BOOL,new TreeSet<Integer>(),new TreeSet<Integer>());
		this.polarity = polarity;
		value = (polarity ? evaluator.trueValue() : evaluator.falseValue());
	}

	@Override
	public EvaluatableValue getValue() {
		return value;
	}

	boolean checkValue(EvaluatableValue value) {
		boolean res = polarity ? ((BooleanTypeInterface) value).isTrue() : ((BooleanTypeInterface) value).isFalse();
		//System.out.println(ID.location() + "Asserting (" + value + " == " + polarity + ") = " + (res? "OK" : "Failed"));
		return res;
		// return polarity ? value.isTrue() : value.isFalse();
	}
	
	@Override
	public int stepValue(Expr expr, ContainsEvaluatableValue[] preState, ContainsEvaluatableValue[] currState) {
		evaluator.updatePreState(preState);
		evaluator.updateCurrState(currState);
		EvaluatableValue newValue = (EvaluatableValue) expr.accept(evaluator);
		value = (polarity ? newValue : newValue.not());
		return -1;
	}

	@Override
	public int initValue(Expr expr, ContainsEvaluatableValue[] preState) {
		evaluator.updatePreState(preState);
		EvaluatableValue newValue = (EvaluatableValue)  expr.accept(evaluator.initExtendedEvaluator);
		value = (polarity ? newValue : newValue.not());
		return -1;
	}

	@Override
	public boolean setValue(EvaluatableValue value) {
		assert(checkValue(value));
		return false;
	}

}
