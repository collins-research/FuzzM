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

import jkind.util.BigFraction;

public abstract class EvaluatableValueHierarchy extends EvaluatableValue {
	
	// BxV -> V
	public EvaluatableValue ite(EvaluatableValue left, EvaluatableValue right) {
		throw new IllegalArgumentException();
	}

	public EvaluatableValue getHigh() {
		return this;
	}
	public EvaluatableValue getLow() {
		return this;
	}

	abstract public int signum();
	
	// Z
	abstract public IntegerType newIntegerType(BigInteger value);

	// Q
	abstract public RationalType newRationalType(BigFraction value);
	//abstract public BigFraction rationalValue();

	// B
	abstract public BooleanType newBooleanType (boolean value);
	//abstract public boolean booleanValue();
	abstract public EvaluatableType<BooleanType> newBooleanInterval();

	public abstract EvaluatableValue join(EvaluatableValue right);
	
}
