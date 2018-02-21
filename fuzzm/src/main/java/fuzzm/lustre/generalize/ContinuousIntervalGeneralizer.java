package jfuzz.lustre.generalize;

import java.math.BigInteger;

import jfuzz.lustre.SignalName;
import jfuzz.lustre.evaluation.ConcreteSimulationResults;
import jfuzz.lustre.evaluation.SimulationResults;
import jfuzz.lustre.evaluation.Simulator;
import jfuzz.value.hierarchy.EvaluatableType;
import jfuzz.value.hierarchy.EvaluatableValue;
import jfuzz.value.hierarchy.NumericType;

abstract public class ContinuousIntervalGeneralizer<T extends NumericType<T>> implements ValueGeneralizer<T> {

	Simulator simulator;
	private static final SimulationResults TRUE = new ConcreteSimulationResults();

	@Override
	public EvaluatableType<T> generalize(Simulator simulator, SignalName si, EvaluatableType<T> curr, EvaluatableType<T> maxInterval) {
		this.simulator = simulator;
		//System.err.println(ID.location() + si.name + " is currently " + curr);
		curr = generalizeIntervalLow(si,curr,maxInterval);
		//System.err.println(ID.location() + si.name + " after low generalization " + curr);
		curr = generalizeIntervalHigh(si,curr,maxInterval);
		//System.err.println(ID.location() + si.name + " after high generalization " + curr);
		return curr;
	}
	
	abstract protected boolean isZero(T x);
	abstract protected T half(EvaluatableValue x);
	
	protected EvaluatableType<T> generalizeIntervalLow(SignalName si, EvaluatableType<T> curr, EvaluatableType<T> maxInterval) {
		T maxLow = maxInterval.getLow();
		EvaluatableType<T> next = maxLow.newInterval(curr.getHigh());
		if (simulator.isConsistent(si,next,TRUE).isSatisfactory()) {
			return next;
		}
		T a = curr.getLow();
		T b = ((! maxLow.isFinite()) && (maxLow.signum() < 0)) ? getLowerBound(si, curr) : maxLow;
		// Invariant b < true lower bound <= a
		while (true) {
			//System.err.println(ID.location() + b + " < true lower bound <= " + a + " <= " + curr.getLow());
			T delta = half(a.minus(b));
			if (isZero(delta)) {
				return a.newInterval(curr.getHigh());
			}
			@SuppressWarnings("unchecked")
			T guess = (T) a.minus(delta);
			next = guess.newInterval(curr.getHigh());
			if (simulator.isConsistent(si, next,TRUE).isSatisfactory()) {
				a = guess;
			} else {
				b = guess;
			}
		}
	}

	protected EvaluatableType<T> generalizeIntervalHigh(SignalName si, EvaluatableType<T> curr, EvaluatableType<T> maxInterval) {
		T maxHigh = maxInterval.getHigh();
		EvaluatableType<T> next = curr.getLow().newInterval(maxHigh);
		if (simulator.isConsistent(si, next,TRUE).isSatisfactory()) {
			return next;
		}

		T a = curr.getHigh();
		T b = ((! maxHigh.isFinite()) && (maxHigh.signum() > 0)) ? getUpperBound(si, curr) : maxHigh;
		// Invariant a <= true upper bound < b
		while (true) {
			//System.err.println(ID.location() + curr.getHigh() + " <= " + a + " <= true upper bound < " + b);
			T delta = half(b.minus(a));
			if (isZero(delta)) {
				return curr.getLow().newInterval(a);
			}
			T guess = (T) a.plus(delta);
			next = curr.getLow().newInterval(guess);
			if (simulator.isConsistent(si, next,TRUE).isSatisfactory()) {
				a = guess;
			} else {
				b = guess;
			}
		}
	}
	
	private T getUpperBound(SignalName si, EvaluatableType<T> curr) {
		T high = curr.getHigh();
		T gap  = high.valueOf(BigInteger.ONE);
		T two  = high.valueOf(BigInteger.valueOf(2));
		while (true) {
			high = high.plus(gap);
			gap = gap.multiply(two);
			EvaluatableType<T> next = curr.getLow().newInterval(high);
			//System.out.println(ID.location() + "Checking Interval (upper) : " + next);
			if (simulator.isConsistent(si, next,TRUE).isSatisfactory()) {
				curr = next;
			} else {
				return high;
			}
		}
	}
	
	private T getLowerBound(SignalName si, EvaluatableType<T> curr) {
		T low = curr.getLow();
		T gap  = low.valueOf(BigInteger.ONE);
		T two  = low.valueOf(BigInteger.valueOf(2));
		while (true) {
			@SuppressWarnings("unchecked")
			T val = (T) low.minus(gap);
			low = val;
			gap = gap.multiply(two);
			EvaluatableType<T> next = low.newInterval(curr.getHigh());
			//System.out.println(ID.location() + "Checking Interval (lower) : " + next);
			if (simulator.isConsistent(si, next,TRUE).isSatisfactory()) {
				curr = next;
			} else {
				return low;
			}
		}
	}

}
