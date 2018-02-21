package jfuzz.value.bound;

import java.util.SortedSet;
import java.util.TreeSet;

import jfuzz.lustre.evaluation.IndexedEvaluator;
import jfuzz.value.hierarchy.EvaluatableValue;
import jkind.lustre.Expr;
import jkind.lustre.Type;

public abstract class BoundValue implements ContainsEvaluatableValue {
	// Before use the visitor must be bound;
	protected IndexedEvaluator evaluator;
	public final SortedSet<Integer> defSet;
	public final SortedSet<Integer> nextSet;
	public final Type type;
	public BoundValue(IndexedEvaluator evaluator, Type type, SortedSet<Integer> defSet, SortedSet<Integer> nextSet) {
		this.evaluator = evaluator;
		this.type = type;
		this.defSet = (defSet == null) ? new TreeSet<Integer>() : defSet;
		this.nextSet = (nextSet == null) ? new TreeSet<Integer>()  : nextSet;
	}

	// -1 : constraint (change?)
	//  0 : no change
	// +1 : change
	abstract public int stepValue(Expr expr, ContainsEvaluatableValue preState[], ContainsEvaluatableValue currState[]);
	abstract public int initValue(Expr expr, ContainsEvaluatableValue binding[]);

	abstract public EvaluatableValue getValue();
	abstract public boolean setValue(EvaluatableValue value);

	@Override
	public String toString() {
		return getValue().toString();
	}

}

