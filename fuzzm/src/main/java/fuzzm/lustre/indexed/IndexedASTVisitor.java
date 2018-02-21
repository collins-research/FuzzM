package jfuzz.lustre.indexed;

import jkind.lustre.visitors.AstVisitor;

public interface IndexedASTVisitor<A,E extends A> extends AstVisitor<A,E> {
	public IndexedVarDecl visit(IndexedVarDecl e);
}
