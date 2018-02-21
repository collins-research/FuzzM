package jfuzz.lustre.generalize;

import jfuzz.lustre.SignalName;
import jfuzz.lustre.evaluation.Simulator;
import jfuzz.value.hierarchy.EvaluatableType;
import jfuzz.value.hierarchy.InstanceType;

interface ValueGeneralizer<T extends InstanceType<T>> {

	abstract public EvaluatableType<T> generalize(Simulator simulator, SignalName si, EvaluatableType<T> curr, EvaluatableType<T> maxInterval);
	
}
