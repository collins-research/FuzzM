package jfuzz.value.hierarchy;

import jkind.lustre.BinaryOp;
import jkind.lustre.Type;
import jkind.lustre.UnaryOp;
import jkind.lustre.values.Value;

public abstract class EvaluatableValue extends Value {
	
	@Override
	public EvaluatableValue applyBinaryOp(BinaryOp op, Value arg) {
		EvaluatableValue right = (EvaluatableValue) arg;
		switch (op) {
	    case PLUS:
	    	return plus(right);
	    case MINUS:
	    	return minus(right);
	    case MULTIPLY:
	    	return multiply(right);
	    case DIVIDE:
	    	return divide(right);
	    case INT_DIVIDE:
	    	return int_divide(right);
	    case MODULUS:
	    	return modulus(right);
	    case EQUAL:
	    	return equalop(right);
	    case NOTEQUAL:
	    	return notequalop(right);
	    case GREATER:
	    	return greater(right);
	    case LESS:
	    	return less(right);
	    case GREATEREQUAL:
	    	return greaterequal(right);
	    case LESSEQUAL:
	    	return lessequal(right);
	    case OR:
	    	return or(right);
	    case AND:
	    	return and(right);
	    case XOR:
	    	return xor(right);
	    case IMPLIES:
	    	return implies(right);
	    case ARROW:
	    	return arrow(right);
		}
		throw new IllegalArgumentException();
	}

	@Override
	public EvaluatableValue applyUnaryOp(UnaryOp op) {
		switch (op) {
		case NEGATIVE: {
			return negate();
		}
		case NOT: {
			return not();
		}
		case PRE: {
			return pre();
		}
		}
		throw new IllegalArgumentException();
	}
	
	public EvaluatableValue arrow(EvaluatableValue right) {
		throw new IllegalArgumentException();
	}
	
	public EvaluatableValue pre() {
		throw new IllegalArgumentException();
	}
	
	// N -> Q
	public EvaluatableValue divide(EvaluatableValue right) {
		throw new IllegalArgumentException();
	}
	
	// N -> N
	public EvaluatableValue multiply(EvaluatableValue right) {
		throw new IllegalArgumentException();
	}
	public EvaluatableValue plus(EvaluatableValue right) {
		throw new IllegalArgumentException();
	}
	public EvaluatableValue negate() {
		throw new IllegalArgumentException();
	}
	public EvaluatableValue minus(EvaluatableValue right) {
		return plus(right.negate());
	}

	// V -> B
	abstract public EvaluatableValue equalop(EvaluatableValue right);

	public EvaluatableValue notequalop(EvaluatableValue right) {
		return equalop(right).not();
	}

	// N -> B
	public EvaluatableValue less(EvaluatableValue right) {
		throw new IllegalArgumentException();
	}
	public EvaluatableValue greater(EvaluatableValue right) {
		throw new IllegalArgumentException();
	}
	public EvaluatableValue greaterequal(EvaluatableValue right) {
		return less(right).not();
	}
	public EvaluatableValue lessequal(EvaluatableValue right) {
		return greater(right).not();
	}
	
	// Z -> Z
	public EvaluatableValue int_divide(EvaluatableValue right) {
		throw new IllegalArgumentException();
	}
	public EvaluatableValue modulus(EvaluatableValue right) {
		throw new IllegalArgumentException();
	}

	// B -> B
	public EvaluatableValue and(EvaluatableValue right) {
		throw new IllegalArgumentException();
	}
	public EvaluatableValue or(EvaluatableValue right) {
		throw new IllegalArgumentException();
	}
	public EvaluatableValue not() {
		throw new IllegalArgumentException();
	}
	public EvaluatableValue xor(EvaluatableValue right) {
		return equalop(right).not();
	}
	public EvaluatableValue implies(EvaluatableValue right) {
		return not().or(right);
	}	

	// Helper Functions

	abstract public EvaluatableValue cast(Type type);

	abstract public Type getType();
	
	@Override
	abstract public boolean equals(Object x);

	@Override
	abstract public int hashCode();

	@Override
	abstract public String toString();
	
}
