package jfuzz.lustre.evaluation;

import jfuzz.value.hierarchy.BooleanTypeInterface;
import jfuzz.value.hierarchy.EvaluatableValue;
import jfuzz.value.instance.BooleanValue;

public class PolySimulationResults extends SimulationResults {

	public EvaluatableValue result;
	
	public PolySimulationResults() {
		result = BooleanValue.TRUE;
	}
	
	private PolySimulationResults(EvaluatableValue result) {
		this.result = result;
	}
	
	@Override
	public PolySimulationResults and(EvaluatableValue result) {
		EvaluatableValue res = this.result.and(result);
		//if (Debug.isEnabled()) System.out.println(ID.location() + "Accumulated Simulation Results : " + res);
		return new PolySimulationResults(res);
	}

	@Override
	public boolean isSatisfactory() {
		return (! ((BooleanTypeInterface) result).isFalse());
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
