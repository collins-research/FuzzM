package jfuzz.util;

import java.util.ArrayList;
import java.util.List;

import jfuzz.lustre.ExprSignal;
import jfuzz.lustre.ExprVect;
import jfuzz.lustre.SignalName;
import jkind.util.BigFraction;

public class IntervalVector extends Vector<JFuzzInterval> implements Copy<IntervalVector> {
	// DAG : this should extend Vector<JFuzzInterval>

	private static final long serialVersionUID = 1991897878162721964L;
	
	public IntervalVector() {
		super();
	}
	
	public ExprVect getExprVector() {
		ExprVect res = new ExprVect();
		for (TypedName name: keySet()) {
			res.put(name,Rat.cast(name.name,get(name).type));
		}
		return res;
	}
	
	public ExprSignal getExprSignal(int k) {
		ExprVect v = getExprVector();
		ExprSignal res = new ExprSignal();
		for (int i=0;i<k;i++) {
			res.add(v);
		}
		return res;
	}
	
	public List<SignalName> elaborate(int k) {
		List<SignalName> res = new ArrayList<>();
		for (int i=0;i<k;i++) {
			for (TypedName key: keySet()) {
				res.add(new SignalName(key,i));
			}
		}
		return res;
	}
	
	public IntervalVector(IntervalVector x) {
		super();
		for (TypedName key: x.keySet()) {
			put(key,x.get(key));
		}
	}
	
	@Override
	public String toString() {
		String res = "(\n";
		for (TypedName key: keySet()) {
			res += "  " + key + ":" + get(key).toString() + "\n";
		}
		return res + ")\n"; 
	}

	@Override
	public IntervalVector copy() {
		return new IntervalVector(this);
	}

	@Override
	public Vector<JFuzzInterval> add(Vector<JFuzzInterval> x) {
		assert(false);
		return null;
	}

	@Override
	public Vector<JFuzzInterval> sub(Vector<JFuzzInterval> x) {
		assert(false);
		return null;
	}

	@Override
	public Vector<JFuzzInterval> mul(BigFraction x) {
		assert(false);
		return null;
	}

}
