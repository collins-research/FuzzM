package jfuzz.value.hierarchy;

public interface RationalTypeInterface {
	
	public EvaluatableType<RationalType> divide(EvaluatableValue right);
	public EvaluatableType<RationalType> divide2(RationalType left);
	public EvaluatableType<RationalType> divide2(RationalIntervalType left);

}
