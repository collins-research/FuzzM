package jfuzz.poly;

public class OpType {
	
	final String name;
	public static final OpType AND = new OpType("and");
	public static final OpType OR  = new OpType("or");

	protected OpType(String name) {
		this.name = name;
	}

	public OpType not() {
		return ((this == AND) ? OR : AND);
	}
	
	public boolean op(boolean x, boolean y) {
		return (this == OR) ? x | y : x & y;
	}
}
