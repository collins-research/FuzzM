package jfuzz.util;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import jfuzz.lustre.SignalName;
import jfuzz.value.hierarchy.EvaluatableValue;
import jfuzz.value.instance.BooleanValue;
import jfuzz.value.instance.IntegerValue;
import jfuzz.value.instance.RationalValue;
import jkind.lustre.NamedType;
import jkind.lustre.Type;
import jkind.util.BigFraction;

public class RatVect extends Vector<BigFraction> implements Copy<RatVect> {
 
	private static final long serialVersionUID = -2872956873023967593L;

	public RatVect() {
		super();
	}
	
	public RatVect(RatVect x) {
		super(x);
	}
	
	public BigFraction maxAbs() {
		BigFraction max = BigFraction.ZERO;
		for (TypedName key: keySet()) {
			BigFraction vmax = get(key);
			vmax = vmax.signum() < 0 ? vmax.negate() : vmax;
			max = max.compareTo(vmax) < 0 ? vmax : max;
		}
		return max;
	}
	
	public static RatVect uniformRandom(IntervalVector S) {
		RatVect res = new RatVect();
		for (TypedName key: S.keySet()) {
			res.put(key,S.get(key).uniformRandom());
		}
		return res;
	}
	
	public BigFraction dot(Vector<BigFraction> x) {
		BigFraction res = BigFraction.ZERO;
		for (TypedName key: keySet()) {
			res = res.add(get(key).multiply(x.get(key)));
		}
		return res;
	}
	
	private static final BigFraction HALF = new BigFraction(BigInteger.ONE,BigInteger.valueOf(2));
	private static BigFraction round(BigFraction x) {
		int sign = x.signum();
		BigFraction res = (sign < 0) ? x.negate() : x;
		BigInteger N = res.add(HALF).floor();
		res = new BigFraction((sign < 0) ? N.negate() : N);
		return res;
	}
	
	public RatVect round() {
		RatVect res = new RatVect();
		for (TypedName key: keySet()) {
			res.put(key,round(get(key)));
		}
		return res;
	}

	@Override
	public RatVect mul(BigFraction M) {
		RatVect res = new RatVect();
		for (TypedName key: keySet()) {
			res.put(key,get(key).multiply(M));
		}
		return res;
	}

	@Override
	public RatVect add(Vector<BigFraction> x) {
		RatVect res = new RatVect();
		Set<TypedName> keys = new HashSet<TypedName>(keySet());
		keys.addAll(x.keySet());
		for (TypedName key: keys) {
			res.put(key,get(key).add(x.get(key)));
		}
		return res;
	}

	@Override
	public RatVect sub(Vector<BigFraction> x) {
		RatVect res = new RatVect();
		Set<TypedName> keys = new HashSet<TypedName>(keySet());
		keys.addAll(x.keySet());
		for (TypedName key: keys) {
			res.put(key,get(key).subtract(x.get(key)));
		}
		return res;
	}
	
	@Override
	public BigFraction get(TypedName key) {
		if (containsKey(key)) {
			return super.get(key);
		}
		//System.out.println(key + " not among [" + String.join(",", keySet()) + "]");
		//assert(false);
		return BigFraction.ZERO;
	}
	
	public List<SignalName> signalNames(int time) {
		List<SignalName> res = new ArrayList<>();
		for (TypedName name: keySet()) {
			res.add(new SignalName(name,time));
		}
		return res;
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
	public RatVect copy() {
		return new RatVect(this);
	}

	private static EvaluatableValue evaluatableValue(Type type, BigFraction value) {
		if (type == NamedType.BOOL) {
			return (value.signum() != 0) ? BooleanValue.TRUE : BooleanValue.FALSE;
		}
		if (type == NamedType.INT) {
			return new IntegerValue(value.floor());
		}
		if (type == NamedType.REAL) {
			return new RationalValue(value);
		}
		throw new IllegalArgumentException();
	}
	
	public EvaluatableVector evaluatableVector() {
		EvaluatableVector res = new EvaluatableVector();
		for (TypedName key: keySet()) {
			res.put(key,evaluatableValue(key.type,get(key)));
		}
		return res;
	}

	
}
