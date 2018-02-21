package jfuzz.util;

import java.util.HashMap;

import jkind.util.BigFraction;

public abstract class Vector<T> extends HashMap<TypedName,T> {

	private static final long serialVersionUID = 1L;
	
	public Vector() {
		super();
	}
	
	public Vector(Vector<T> arg) {
		super();
		for (TypedName key: arg.keySet()) {
			this.put(key,arg.get(key));
		}
	}
	
	@Override
	public boolean containsKey(Object arg) {
		throw new IllegalArgumentException();
	}
	
	public boolean containsKey(TypedName arg) {
		return super.containsKey(arg);
	}
	
	@Override
	public T get(Object key) {
		throw new IllegalArgumentException();
	}
	
	public T get(TypedName key) {
		return super.get(key);
	}
	
	//abstract public ACExprCtx dot(Vector<T> x);
	abstract public Vector<T> add(Vector<T> x);
	abstract public Vector<T> sub(Vector<T> x);
	abstract public Vector<T> mul(BigFraction x);
	
	public int bytes() {
		return size();
	}
	
}

