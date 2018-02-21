package jfuzz.lustre.evaluation;

import java.util.SortedSet;

import jfuzz.lustre.indexed.IndexedIdExpr;
import jfuzz.value.bound.ComputedValue;
import jfuzz.value.bound.ConstrainedValue;
import jfuzz.value.bound.ContainsEvaluatableValue;
import jfuzz.value.bound.InputValue;
import jfuzz.value.hierarchy.EvaluatableValue;
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
