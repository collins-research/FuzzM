package jfuzz.lustre.evaluation;

import jfuzz.value.hierarchy.BooleanTypeInterface;
import jfuzz.value.hierarchy.EvaluatableValue;

abstract public class SimulationResults {
	abstract public SimulationResults and(EvaluatableValue result);
	abstract public boolean isSatisfactory();
	abstract public BooleanTypeInterface result();
	@Override
	abstract public String toString();
}
