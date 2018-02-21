package jfuzz.value.instance;

import jfuzz.value.hierarchy.BooleanType;
import jfuzz.value.hierarchy.EvaluatableType;
import jfuzz.value.hierarchy.EvaluatableValue;

public interface BooleanValueInterface {

	EvaluatableType<BooleanType> not();
	
	EvaluatableType<BooleanType> equalop(EvaluatableValue right);
	EvaluatableType<BooleanType> equalop2(BooleanValue left);
	EvaluatableType<BooleanType> equalop2(BooleanInterval left);

	EvaluatableType<BooleanType> and(EvaluatableValue right);
	EvaluatableType<BooleanType> and2(BooleanValue left);
	EvaluatableType<BooleanType> and2(BooleanInterval left);

	EvaluatableType<BooleanType> or(EvaluatableValue right);
	EvaluatableType<BooleanType> or2(BooleanValue left);
	EvaluatableType<BooleanType> or2(BooleanInterval left);

}
