package jfuzz.value.hierarchy;

public interface Joinable<T extends InstanceType<T>> {
	public EvaluatableType<T> join(EvaluatableValue right);
	public EvaluatableType<T> join2(IntervalType<T> left);
	public EvaluatableType<T> join2(T left);
}
