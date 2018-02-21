/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.lustre;

import java.math.BigDecimal;

import jkind.lustre.BinaryExpr;
import jkind.lustre.BinaryOp;
import jkind.lustre.BoolExpr;
import jkind.lustre.CastExpr;
import jkind.lustre.Equation;
import jkind.lustre.Expr;
import jkind.lustre.IdExpr;
import jkind.lustre.IntExpr;
import jkind.lustre.NamedType;
import jkind.lustre.RealExpr;
import jkind.lustre.UnaryExpr;
import jkind.lustre.UnaryOp;
import jkind.lustre.VarDecl;

public class ExprCtx extends LustreCtx {
	
	private Expr defaultExpr;
	NamedType type;
	
	protected static Expr defaultValue(NamedType type) {
		// We use "true" for boolean default because our AC is usually AND
		if (type == NamedType.BOOL) return new BoolExpr(true);
		if (type == NamedType.INT)  return new IntExpr(0);
		if (type == NamedType.REAL) return new RealExpr(BigDecimal.ZERO);
		assert(false);
		return null;
	}

	public ExprCtx(NamedType type) {
		this.type = type;
		defaultExpr = defaultValue(type);
	}

	public ExprCtx(NamedType type, Expr defaultValue) {
		this.type = type;
		defaultExpr = defaultValue;
	}

	public ExprCtx(NamedType type, LustreCtx arg) {
		super(arg);
		this.type = type;
		defaultExpr = defaultValue(type);
	}
	
	public ExprCtx(ExprCtx arg) {
		super(arg);
		this.type = arg.type;
		this.defaultExpr = arg.getExpr();
	}
	
	public Expr getExpr() {
		return defaultExpr;
	}

	public void setExpr(Expr expr) {
		this.defaultExpr = expr;
	}

	public ExprCtx bind(String varName) {
		IdExpr name = new IdExpr(varName);
		eqs.add(new Equation(name, getExpr()));
		decls.add(new VarDecl(varName,type));
		setExpr(name);
		return this;
	}

	public Expr op(BinaryOp op, Expr arg) {
		Expr res = new BinaryExpr(getExpr(),op,arg);
		setExpr(res);
		switch (op) {
		case EQUAL:
		case NOTEQUAL:
		case GREATER:
		case GREATEREQUAL:
		case LESS:
		case LESSEQUAL:
			this.type = NamedType.BOOL;
		default:
			break;
		}
		return res;
	}

	public Expr op(BinaryOp op, ExprCtx earg) {
		add(earg);
		return op(op,earg.defaultExpr);
	}

	public Expr op(UnaryOp op) {
		Expr res = new UnaryExpr(op,getExpr());
		setExpr(res);
		return res;
	}

	public Expr cast(NamedType type) {
		Expr res = new CastExpr(type,getExpr());
		setExpr(res);
		this.type = type;
		return res;
	}

}
