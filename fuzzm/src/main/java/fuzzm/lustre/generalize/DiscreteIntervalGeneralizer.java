package jfuzz.lustre.generalize;

import jfuzz.lustre.SignalName;
import jfuzz.lustre.evaluation.ConcreteSimulationResults;
import jfuzz.lustre.evaluation.SimulationResults;
import jfuzz.lustre.evaluation.Simulator;
import jfuzz.value.hierarchy.EvaluatableType;
import jfuzz.value.hierarchy.InstanceType;

public class DiscreteIntervalGeneralizer<T extends InstanceType<T>> implements ValueGeneralizer<T> {
	
	private static final SimulationResults TRUE = new ConcreteSimulationResults();

	public EvaluatableType<T> generalize(Simulator simulator, SignalName si, EvaluatableType<T> curr, EvaluatableType<T> maxInterval) {
		if (simulator.isConsistent(si,maxInterval,TRUE).isSatisfactory()) {
			return maxInterval;
		}
		return curr;
	}

}
