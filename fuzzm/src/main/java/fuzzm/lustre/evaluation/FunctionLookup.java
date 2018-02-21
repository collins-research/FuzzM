package jfuzz.lustre.evaluation;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

public class FunctionLookup<T> {

	final private Map<String,Map<EvaluatableArgList,T>> fmap;
	
	public Collection<String> keySet() {
		return fmap.keySet();
	}
	
	public FunctionLookup(Collection<String> fns) {
		fmap = new HashMap<>();
		for (String fn: fns) {
			fmap.put(fn, new HashMap<>());
		}
	}
	
	public Set<EvaluatableArgList> getInstances(String fn) {
		Map<EvaluatableArgList,T> m1 = fmap.get(fn);
		if (m1 == null) throw new IllegalArgumentException();
		return m1.keySet();
	}
	
	public Collection<T> getValues(String fn) {
		Map<EvaluatableArgList,T> m1 = fmap.get(fn);
		if (m1 == null) throw new IllegalArgumentException();
		return m1.values();
	}
	
	public T get(String fn, EvaluatableArgList args) {
		Map<EvaluatableArgList,T> m1 = fmap.get(fn);
		if (m1 == null) throw new IllegalArgumentException(fn + " not found in FunctionLookup " + this.toString());
		T value = m1.get(args);
		if (value == null) throw new IllegalArgumentException(fn + args.toString() + " not found in Map " + toString(fn,m1));
		return value;
	}

	public void set(String fn, EvaluatableArgList args, T value) {
		Map<EvaluatableArgList,T> m1 = fmap.get(fn);
		if (m1 == null) throw new IllegalArgumentException();
		m1.put(args, value);
		fmap.put(fn,m1);
	}

	private String toString(String fn, Map<EvaluatableArgList,T> fmap) {
		String res = "";
		for (EvaluatableArgList arg: fmap.keySet()) {
			res += " " + fn + arg + ": " + fmap.get(arg) + "\n";
		}
		return res;
	}
	
	@Override
	public String toString() {
		String res = "{\n";
		for (String fn: fmap.keySet()) {
			res += toString(fn,fmap.get(fn));
		}
		return res + "}\n";
	}
	
}
