package jfuzz.lustre.evaluation;

import java.util.Arrays;

import jfuzz.lustre.indexed.IndexedIdExpr;
import jfuzz.value.bound.ContainsEvaluatableValue;
import jkind.lustre.IdExpr;
import jkind.lustre.values.Value;

public class InitIndexedEvaluator extends InitEvaluatableValueEvaluator {

	public InitIndexedEvaluator(BaseEvaluatableValueEvaluator evaluator) {
		super(evaluator);
	}

	ContainsEvaluatableValue preState[];
	
	@Override
	public Value visit(IdExpr e) {
		if (preState == null) {
			System.out.println("Unbound State");
			assert(false);
		}
		ContainsEvaluatableValue cev = preState[((IndexedIdExpr) e).index];
		if (cev == null) {
			System.out.println("Unbound Variable : " + e.id + " with index " + ((IndexedIdExpr) e).index);
			System.out.println("Current State : " + Arrays.toString(preState));
			assert(false);
		}
		Value res = cev.getValue();
		if (res == null) {
			System.out.println("Unbound Variable : " + e.id + " with index " + ((IndexedIdExpr) e).index);
			System.out.println("Current State : " + Arrays.toString(preState));
			assert(false);
		}
		return res;
	}

}
