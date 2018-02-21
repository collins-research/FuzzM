package jfuzz.value.instance;

import jfuzz.value.hierarchy.BooleanType;
import jfuzz.value.hierarchy.NumericType;
import jfuzz.value.hierarchy.RationalType;

public interface RationalValueInterface /*extends NumericTypeInterface<RationalType>*/ {

	RationalType divide(RationalType right);
	RationalType divide2(RationalValue left);
	RationalType divide2(RationalInfinity left);

	RationalType plus(NumericType<RationalType> right);
	RationalType plus2(RationalValue left);
	RationalType plus2(RationalInfinity left);

	RationalType multiply(NumericType<RationalType> right);
	RationalType multiply2(RationalValue left);
	RationalType multiply2(RationalInfinity left);

	RationalType max(RationalType right);
	RationalType max2(RationalValue left);
	RationalType max2(RationalInfinity left);

	RationalType min(RationalType right);
	RationalType min2(RationalValue left);
	RationalType min2(RationalInfinity left);

	BooleanType less(NumericType<RationalType> right);
	BooleanType less2(RationalValue left);
	BooleanType less2(RationalInfinity left);

	BooleanType greater(NumericType<RationalType> right);
	BooleanType greater2(RationalValue left);
	BooleanType greater2(RationalInfinity left);

	BooleanType equalop(NumericType<RationalType> right);
	BooleanType equalop2(RationalValue left);
	BooleanType equalop2(RationalInfinity left);

}
