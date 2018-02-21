package jfuzz.util;

import java.util.ArrayList;
import java.util.List;

import jfuzz.lustre.SignalName;
import jfuzz.value.hierarchy.EvaluatableValue;

public class EvaluatableSignal extends Signal<EvaluatableVector> {

	public EvaluatableSignal(Signal<EvaluatableVector> x) {
		super(x);
	}

	public EvaluatableSignal() {
		super();
	}

	private static final long serialVersionUID = -7514024314823844551L;

	public RatSignal ratSignal() {
		RatSignal res = new RatSignal();
		for (int time=0;time<size();time++) {
			res.add(get(time).ratVector());
		}
		return res;
	}

	@Override
	public EvaluatableVector get(int i) {
		if (i < size()) {
			return super.get(i);
		}
		return new EvaluatableVector();
	}

	public EvaluatableValue get(TypedName name, int time)  {
		EvaluatableVector slice = get(time);
		return slice.get(name);
	}

	public void set(TypedName name, int time, EvaluatableValue value) {
		EvaluatableVector curr = get(time);
		curr.put(name, value);
		if (time < size()) {
			super.set(time,curr);
			return;
		}
		for (int i=size();i<time;i++) {
			add(new EvaluatableVector());
		}
		add(curr);
	}
	
	@Override
	public EvaluatableVector set(int time, EvaluatableVector value) {
		if (time < size()) {
			return super.set(time,value);
		}
		for (int i=size();i<time;i++) {
			add(new EvaluatableVector());
		}
		add(value);
		return value;
	}
	
	public void normalize(EvaluatableSignal arg) {
		for (int time=0;time<arg.size();time++) {
			EvaluatableVector res = get(time);
			res.normalize(arg.get(time));
			set(time,res);
		}
	}
	
	public List<SignalName> getSignalNames() {
		List<SignalName> res = new ArrayList<>();
		for (int time=0;time<size();time++) {
			EvaluatableVector ev = get(time);
			for (TypedName name: ev.keySet()) {
				res.add(new SignalName(name, time));
			}
		}
		return res;
	}
	
}
