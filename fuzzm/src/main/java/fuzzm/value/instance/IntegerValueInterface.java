package jfuzz.value.instance;

import jfuzz.value.hierarchy.BooleanType;
import jfuzz.value.hierarchy.EvaluatableType;
import jfuzz.value.hierarchy.IntegerType;
import jfuzz.value.hierarchy.NumericType;

public interface IntegerValueInterface /*extends NumericTypeInterface<IntegerType>*/ {
	
	IntegerType int_divide(IntegerType right);
	IntegerType int_divide2(IntegerValue left);
	IntegerType int_divide2(IntegerInfinity left);
	
	EvaluatableType<IntegerType> modulus(IntegerType right);
	IntegerType modulus2(IntegerValue left);
	EvaluatableType<IntegerType> modulus2(IntegerInfinity left);
	
	IntegerType max(IntegerType right);
	IntegerType max2(IntegerValue left);
	IntegerType max2(IntegerInfinity left);

	IntegerType min(IntegerType right);
	IntegerType min2(IntegerValue left);
	IntegerType min2(IntegerInfinity left);

	IntegerType multiply(NumericType<IntegerType> right);
	IntegerType multiply2(IntegerValue left);
	IntegerType multiply2(IntegerInfinity left);
	
	IntegerType plus(NumericType<IntegerType> right);
	IntegerType plus2(IntegerValue left);
	IntegerType plus2(IntegerInfinity left);
	
	BooleanType less(NumericType<IntegerType> right);
	BooleanType less2(IntegerValue left);
	BooleanType less2(IntegerInfinity left);
	
	BooleanType greater(NumericType<IntegerType> right);
	BooleanType greater2(IntegerValue left);
	BooleanType greater2(IntegerInfinity left);
	
	BooleanType equalop(NumericType<IntegerType> right);
	BooleanType equalop2(IntegerValue left);
	BooleanType equalop2(IntegerInfinity left);

}
