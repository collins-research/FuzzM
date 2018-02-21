package jfuzz.value.instance;

import jfuzz.value.hierarchy.BooleanType;
import jfuzz.value.hierarchy.EvaluatableType;

public interface PolyBooleanValueInterface extends BooleanValueInterface {

	EvaluatableType<BooleanType> equalop2(PolyBooleanValue left);
	EvaluatableType<BooleanType> and2(PolyBooleanValue left);
	EvaluatableType<BooleanType> or2(PolyBooleanValue right);

}
