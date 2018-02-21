package jfuzz.lustre.generalize;

import java.math.BigInteger;

import jfuzz.value.hierarchy.EvaluatableValue;
import jfuzz.value.hierarchy.EvaluatableValueHierarchy;
import jfuzz.value.hierarchy.RationalType;
import jfuzz.value.instance.RationalValue;
import jkind.util.BigFraction;

public class RationalIntervalGeneralizer extends ContinuousIntervalGeneralizer<RationalType> {
	
	public static final RationalType RATIONAL_EPSILON = new RationalValue(new BigFraction(BigInteger.ONE, BigInteger.valueOf(10000)));
	public static final RationalType TWO = new RationalValue(new BigFraction(BigInteger.valueOf(2)));

	@Override
	protected boolean isZero(RationalType x) {
		return ((EvaluatableValueHierarchy)x.abs().minus(RATIONAL_EPSILON)).signum() < 0;
	}

	@Override
	protected RationalType half(EvaluatableValue x) {
		return ((RationalType) x).divide(TWO);
	}

}
