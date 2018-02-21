package jfuzz.lustre.indexed;

import jkind.lustre.visitors.ExprVisitor;

public interface IndexedExprVisitor<T> extends ExprVisitor<T> {
	public T visit(IndexedIdExpr e);
}
