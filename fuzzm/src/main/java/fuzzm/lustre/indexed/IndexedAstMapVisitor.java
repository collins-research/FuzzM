package jfuzz.lustre.indexed;


import jkind.lustre.Ast;
import jkind.lustre.Expr;
import jkind.lustre.IdExpr;
import jkind.lustre.VarDecl;
import jkind.lustre.visitors.AstMapVisitor;

public class IndexedAstMapVisitor extends AstMapVisitor implements IndexedExprVisitor<Expr>,IndexedASTVisitor<Ast,Expr> {

	@Override
	public Expr visit(IndexedIdExpr e) {
		Expr res = visit((IdExpr) e);
		if (res instanceof IndexedIdExpr) {
			return res;
		}
		return new IndexedIdExpr((IdExpr) res,e.index);
	}
	
	@Override
	public IndexedVarDecl visit(IndexedVarDecl e) {
		VarDecl res = visit((VarDecl) e);
		if (res instanceof IndexedVarDecl) {
			return (IndexedVarDecl) res;
		}
		return new IndexedVarDecl((VarDecl) res,e.index);
	}

}
