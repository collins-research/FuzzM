package jfuzz.lustre.indexed;

import jkind.lustre.IdExpr;

public class IndexedIdExpr extends IdExpr {
	public int index;
	public IndexedIdExpr(IdExpr x, int index) {
		super(x.location,x.id);
		this.index = index;
	}
	public IndexedIdExpr(String id, int index) {
		super(id);
		this.index = index;
	}
	public <T> T accept(IndexedExprVisitor<T> visitor) {
		return visitor.visit(this);
	}
	public String toString() {
		return super.toString() + "<" + index + ">";
	}
}
