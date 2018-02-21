package jfuzz.util;

import java.util.ArrayList;

public abstract class Signal<V extends Copy<V>> extends ArrayList<V> {

	private static final long serialVersionUID = 1L;
	
	public Signal(Signal<V> x) {
		super();
		for (V v: x) {
			add(v.copy());
		}
	}
	
	public Signal() {
		super();
	}

	public int bytes() {
		int res = 0;
		for (V v: this) {
			res += v.bytes();
		}
		return res;
	}
	
}
