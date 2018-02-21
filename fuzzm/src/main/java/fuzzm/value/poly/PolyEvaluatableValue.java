package jfuzz.value.poly;

import jfuzz.value.hierarchy.EvaluatableValue;
import jkind.util.BigFraction;

public abstract class PolyEvaluatableValue extends EvaluatableValue implements Comparable<PolyEvaluatableValue> {

	public abstract BigFraction cex();
	
	@Override
	public int compareTo(PolyEvaluatableValue o) {
		return cex().compareTo(o.cex());
	}

	public abstract String toACL2();

}
