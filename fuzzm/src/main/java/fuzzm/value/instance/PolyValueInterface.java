package jfuzz.value.instance;

import jfuzz.value.hierarchy.BooleanType;
import jfuzz.value.hierarchy.IntegerType;

public interface PolyValueInterface extends IntegerValueInterface {

	IntegerType int_divide2(PolyValue left);
	IntegerType modulus2(PolyValue left);
	IntegerType max2(PolyValue left);
	IntegerType min2(PolyValue left);
	IntegerType multiply2(PolyValue left);
	IntegerType plus2(PolyValue left);
	BooleanType less2(PolyValue left);
	BooleanType greater2(PolyValue left);
	BooleanType equalop2(PolyValue left);
}
