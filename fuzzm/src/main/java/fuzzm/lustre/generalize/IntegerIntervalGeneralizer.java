package jfuzz.lustre.generalize;

import java.math.BigInteger;

import jfuzz.value.hierarchy.EvaluatableValue;
import jfuzz.value.hierarchy.IntegerType;
import jfuzz.value.instance.IntegerValue;

public class IntegerIntervalGeneralizer extends ContinuousIntervalGeneralizer<IntegerType> {

	@Override
	protected boolean isZero(IntegerType x) {
		boolean res = (x.signum() == 0);
		//System.out.println(ID.location() + "(" + x + " == 0) = " + res);		
		return res;
	}

	@Override
	protected IntegerType half(EvaluatableValue x) {
		IntegerValue two = new IntegerValue(BigInteger.valueOf(2));
		IntegerType res = (IntegerType) x;
		int sign = res.signum();
		res = res.abs().int_divide(two);
		res = (sign < 0) ? res.negate() : res;
		//System.out.println(ID.location() + "1/2 of " + x + " is " + res);		
		return res;
	}

}
