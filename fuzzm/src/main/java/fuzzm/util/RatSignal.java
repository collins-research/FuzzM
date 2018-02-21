package jfuzz.util;

import java.util.ArrayList;
import java.util.List;

//import jfuzz.legacy.value.EvaluatableValue;
//import jfuzz.legacy.value.RatValue;
//import jfuzz.legacy.value.UnboundFraction;
//import jfuzz.legacy.value.ValueInterval;
import jfuzz.lustre.SignalName;
import jkind.util.BigFraction;
import jkind.util.StreamIndex;

public class RatSignal extends Signal<RatVect> {

	private static final long serialVersionUID = 5365578259283718106L;

	public RatSignal() {
		super();
	}
	
	public RatSignal(RatSignal x) {
		super();
		for (RatVect v: x) {
			add(new RatVect(v));
		}
	}
	
	public EvaluatableSignal evaluatableSignal() {
		EvaluatableSignal res = new EvaluatableSignal();
		for (int time=0;time<size();time++) {
			res.add(get(time).evaluatableVector());
		}
		return res;
	}
	

	public static RatSignal uniformRandom(int size, IntervalVector S) {
		RatSignal res = new RatSignal();
		for (int i=0;i<size;i++) {
			res.add(RatVect.uniformRandom(S));
		}
		return res;
	}
	
	@Override
	public RatVect get(int time) {
		if (time < size()) {
			return super.get(time);
		}
		return new RatVect();
	}
	
	@Override
	public RatVect set(int time, RatVect value) {
		if (time < size()) {
			return super.set(time,value);
		}
		for (int i=size();i<time;i++) {
			add(new RatVect());
		}
		add(value);
		return value;
	}
	
	public BigFraction maxAbs() {
		BigFraction max = BigFraction.ZERO;
		for (RatVect v: this) {
			BigFraction vmax = v.maxAbs();
			max = max.compareTo(vmax) < 0 ? vmax : max;
		}
		return max;
	}
	
	public RatSignal round() {
		RatSignal res = new RatSignal();
		for (RatVect v: this) {
			res.add(v.round());
		}
		return res;
	}	

	public void put(int time, TypedName key, BigFraction value) {
		RatVect vect = get(time);
		vect.put(key, value);
		set(time,vect);
	}
	
	public RatSignal mul(BigFraction M) {
		RatSignal res = new RatSignal();
		for (RatVect v: this) {
			res.add(v.mul(M));
		}
		return res;
	}

	public RatSignal add(RatSignal x) {
		RatSignal res = new RatSignal();
		int size = Math.max(size(),x.size());
		for (int i=0;i<size;i++) {
			res.add(get(i).add(x.get(i)));
		}
		return res;
	}
	
	public RatSignal sub(RatSignal x) {
		RatSignal res = new RatSignal();
		int size = Math.max(size(),x.size());
		for (int i=0;i<size;i++) {
			res.add(get(i).sub(x.get(i)));
		}
		return res;
	}
	
	public BigFraction dot(RatSignal x){		
		RatVect me = this.encode();
		RatVect they = x.encode();
		return me.dot(they);
	}
	
	public RatVect encode() {
		RatVect res = new RatVect();
		for (int time=0;time<size();time++) {
			RatVect vect = get(time);
			for (TypedName key: vect.keySet()) {
				StreamIndex si = new StreamIndex(key.name,time);
				String keyString = si.getEncoded().str;
				res.put(new TypedName(keyString,key.type),vect.get(key));
			}
		}
		return res;
	}	
//	
//	public Map<String,EvaluatableValue>[] ratValues() {
//		int k = size();
//		@SuppressWarnings("unchecked")
//		Map<String,EvaluatableValue> evaluatableValues[] = new HashMap[k];
//		for (int time=0;time<k;time++) {
//			RatVect v = get(time);
//			evaluatableValues[time] = new HashMap<>();
//			for (String key: v.keySet()) {
//				RatValue z = new RatValue(v.get(key));
//				evaluatableValues[time].put(key,z);
//			}
//		}
//		return evaluatableValues;
//	}
//	
//	public Map<String,EvaluatableValue>[] intervalValues() {
//		int k = size();
//		@SuppressWarnings("unchecked")
//		Map<String,EvaluatableValue> evaluatableValues[] = new HashMap[k];
//		for (int time=0;time<k;time++) {
//			RatVect v = get(time);
//			evaluatableValues[time] = new HashMap<>();
//			for (String key: v.keySet()) {
//				ValueInterval z = new ValueInterval(new UnboundFraction(v.get(key)));
//				evaluatableValues[time].put(key,z);
//			}
//		}
//		return evaluatableValues;
//	}
//	
	public List<SignalName> signalNames() {
		List<SignalName> res = new ArrayList<>();
		for (int time=0;time<size();time++) {
			res.addAll(get(time).signalNames(time));
		}
		return res;
	}
	
	@Override
	public String toString() {
		int time = 0;
		String res = "[\n";
		for (RatVect v: this) {
			res += " time:" + time++ + " ";
			res += v.toString();
		}
		return res + "]"; 
	}

}
