/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.value.hierarchy;

import java.math.BigInteger;

import jkind.lustre.NamedType;
import jkind.lustre.Type;

public abstract class IntegerType extends NumericType<IntegerType> implements IntegerTypeInterface {
	
	@Override
	public final EvaluatableType<IntegerType> int_divide(EvaluatableValue right) {
		// System.out.println(ID.location() + this + "/" + right);
		IntegerTypeInterface rv = ((IntegerTypeInterface) right);
		EvaluatableType<IntegerType> res = rv.int_divide2(this);
		//System.out.println(ID.location() + "(" + this + "/" + right + ") = " + res);
		return res;
	}
	@Override
	public final EvaluatableType<IntegerType> int_divide2(IntegerType left) {
		return left.int_divide(this);
	}
	
	@Override
	public final EvaluatableType<IntegerType> int_divide2(IntegerIntervalType left) {
		IntegerType min = left.getLow();
		IntegerType max = left.getHigh();
		IntegerType q1 = min.int_divide(this);
		IntegerType q2 = max.int_divide(this);
		return q1.min(q2).newInterval(q1.max(q2));
	}

	abstract public IntegerType int_divide(IntegerType right);
	
	@Override
	public final EvaluatableType<IntegerType> modulus(EvaluatableValue right) {
		IntegerTypeInterface rv = ((IntegerTypeInterface) right);
		EvaluatableType<IntegerType> res = rv.modulus2(this);
		//System.out.println(ID.location() + "(" + this + "%" + right + ") = " + res);
		return res;
	}

	@Override
	public final EvaluatableType<IntegerType> modulus2(IntegerType left) {
		return left.modulus(this);
	}
	@Override
	public final EvaluatableType<IntegerType> modulus2(IntegerIntervalType left) {
		int sign = signum();
		IntegerType modulus = (sign < 0) ? negate() : this;
		IntegerType max = (IntegerType) modulus.minus(newIntegerType(BigInteger.ONE));
		IntegerType min = newIntegerType(BigInteger.ZERO);
		return min.newInterval(max);
	}

	abstract public EvaluatableType<IntegerType> modulus(IntegerType right);
	
	@Override
	public final Type getType() {
		return NamedType.INT;
	}
	
}
