package jfuzz.lustre.evaluation;

import jfuzz.value.hierarchy.BooleanTypeInterface;
import jfuzz.value.hierarchy.EvaluatableValue;
import jfuzz.value.instance.BooleanValue;

public class ConcreteSimulationResults extends SimulationResults {

	EvaluatableValue result;
	
	public ConcreteSimulationResults() {
		result = BooleanValue.TRUE;
	}
	
	private ConcreteSimulationResults(EvaluatableValue result) {
		this.result = result;
	}
	
	@Override
	public ConcreteSimulationResults and(EvaluatableValue result) {
		return new ConcreteSimulationResults(this.result.and(result));
	}

	@Override
	public boolean isSatisfactory() {
		return ((BooleanTypeInterface) result).isTrue();
	}

	@Override
	public BooleanTypeInterface result() {
		return (BooleanTypeInterface) result;
	}

	@Override
	public String toString() {
		return result.toString();
	}

}
