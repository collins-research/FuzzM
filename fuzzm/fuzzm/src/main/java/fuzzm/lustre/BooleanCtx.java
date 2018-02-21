/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.lustre;

import java.util.Collection;

import jkind.lustre.BinaryExpr;
import jkind.lustre.BinaryOp;
import jkind.lustre.Expr;
import jkind.lustre.NamedType;

public class BooleanCtx extends ACExprCtx {
	
	public BooleanCtx() {
		super(NamedType.BOOL,BinaryOp.AND);
	}
	
	public BooleanCtx(Expr initialValue) {
		this();
		add(initialValue);
	}
	
	public BooleanCtx(Collection<Expr> initialValue) {
		this();
		addAll(initialValue);
	}
	
	public BooleanCtx(ExprCtx arg) {
		super(BinaryOp.AND,arg);
	}
	
	public BooleanCtx implies(ExprCtx x) {
		BooleanCtx res = new BooleanCtx(this);
		res.eqs.addAll(x.eqs);
		res.decls.addAll(x.decls);
		Expr exp = new BinaryExpr(getExpr(),BinaryOp.IMPLIES,x.getExpr());
		res.exprList.clear();
		res.exprList.add(exp);
		return res;
	}
	
	public BooleanCtx implies(Expr x) {
		BooleanCtx res = new BooleanCtx(this);
		Expr exp = new BinaryExpr(getExpr(),BinaryOp.IMPLIES,x);
		res.exprList.clear();
		res.exprList.add(exp);
		return res;
	}
	
	public void and(Expr expr) {
		add(expr);
	}
	
}
