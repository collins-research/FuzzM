package jfuzz.util;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;

import jfuzz.value.hierarchy.EvaluatableType;
import jfuzz.value.hierarchy.EvaluatableValue;
import jfuzz.value.hierarchy.RationalType;
import jfuzz.value.instance.RationalValue;
import jkind.lustre.NamedType;
import jkind.util.BigFraction;

public class EvaluatableVector extends Vector<EvaluatableValue> implements Copy<EvaluatableVector>{

	private static final long serialVersionUID = 4232014853067213712L;

	public EvaluatableVector(EvaluatableVector arg) {
		super(arg);
	}
	
	public EvaluatableVector() {
		super();
	}
	
	@Override
	public Vector<EvaluatableValue> add(Vector<EvaluatableValue> x) {
		EvaluatableVector res = new EvaluatableVector(this);
		Set<TypedName> keys = new HashSet<TypedName>(keySet());
		keys.addAll(x.keySet());
		for (TypedName key: keys) {
			res.put(key,get(key).plus(x.get(key)));
		}
		return res;
	}

	@Override
	public Vector<EvaluatableValue> sub(Vector<EvaluatableValue> x) {
		EvaluatableVector res = new EvaluatableVector(this);
		Set<TypedName> keys = new HashSet<TypedName>(keySet());
		keys.addAll(x.keySet());
		for (TypedName key: keys) {
			res.put(key,get(key).minus(x.get(key)));
		}
		return res;
	}

	@Override
	public Vector<EvaluatableValue> mul(BigFraction x) {
		EvaluatableVector res = new EvaluatableVector(this);
		RationalType M = new RationalValue(x);
		for (TypedName key: keySet()) {
			// This converts the whole vector to a real .. which we
			// are probably doing anyway if we are doing vector math.
			res.put(key,get(key).cast(NamedType.REAL).multiply(M));
		}
		return res;
	}
	
	public EvaluatableValue get(TypedName key) {
		assert(key instanceof TypedName);
		if (containsKey(key)) {
			return super.get(key);
		}
		Collection<String> names = keySet().stream().map(TypedName::toString).collect(Collectors.toList());
		System.out.println(key + " not among [" + String.join(",", names) + "]");
		throw new IndexOutOfBoundsException();
	}

	@Override
	public EvaluatableVector copy() {
		return new EvaluatableVector(this);
	}

	public RatVect ratVector() {
		RatVect res = new RatVect();
		for (TypedName name: keySet()) {
			res.put(name, ((RationalValue) ((EvaluatableType<?>) get(name)).rationalType()).value());
		}
		return res;
	}

	public void normalize(EvaluatableVector arg) {
		for (TypedName name : arg.keySet()) {
			if (! containsKey(name)) {
				put(name,arg.get(name));
			}
		}
	}

}
