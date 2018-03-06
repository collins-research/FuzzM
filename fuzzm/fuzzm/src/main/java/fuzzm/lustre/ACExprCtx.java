/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.lustre;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import fuzzm.util.IDString;
import jkind.lustre.BinaryExpr;
import jkind.lustre.BinaryOp;
import jkind.lustre.Expr;
import jkind.lustre.NamedType;

public class ACExprCtx extends ExprCtx {

	protected List<Expr> exprList = new ArrayList<>(); 
	protected BinaryOp op;
	
	public ACExprCtx(NamedType type, BinaryOp op, Expr defaultValue) {
		super(type,defaultValue);
		this.op = op;
	}

	public ACExprCtx(NamedType type, BinaryOp op) {
		this(type, op, ExprCtx.defaultValue(type));
	}
	
	public ACExprCtx(BinaryOp op, ExprCtx arg) {
		super(arg);
		this.op = op;
		add(arg.getExpr());
	}
	
	public ACExprCtx(ACExprCtx arg) {
		super(arg);
		exprList = new ArrayList<>(arg.exprList);
		op = arg.op;		
	}
	
	private Expr treeExprRec(int min, int max) {
		int span = max - min;
		if (span == 0) return exprList.get(min);
		if (span == 1) return new BinaryExpr(exprList.get(min),op,exprList.get(max));
		int half = span/2;
		Expr left  = treeExprRec(min,min+half);
		Expr right = treeExprRec(min+half+1,max);
		return new BinaryExpr(left,op,right);
	}
	
	private Expr treeExpr() {
		int size = exprList.size();
		if (size <= 0) return super.getExpr();
		return treeExprRec(0,size-1);
	}
	
	private Expr bindExprRec(int min, int max,int index, IDString base) {
		int span = max - min;
		if (span == 0) return exprList.get(min);
		if (span == 1) return new BinaryExpr(exprList.get(min),op,exprList.get(max));
		int half = span/2;
		Expr left  = bindExprRec(min,min+half,index*2+1,base);
		Expr right = bindExprRec(min+half+1,max,index*2,base);
		Expr res = define(base.index(index),type,new BinaryExpr(left,op,right));
		return res;
	}
	
	@Override
	public ExprCtx bind(IDString base) {
		int size = exprList.size();
		if (size <= 0) return new ExprCtx(super.bind(base));
		Expr lastExpr = bindExprRec(0,size-1,1,base);
		setExpr(lastExpr);
		return new ExprCtx(super.bind(base));
	}
	
	@Override
	public void setExpr(Expr expr) {
		exprList.clear();
		exprList.add(expr);
	}

	@Override
	public Expr getExpr() {
		Expr res = treeExpr();
		return res;
	}

	public void add(Expr expr) {
		exprList.add(expr);
	}
	
	public void add(ACExprCtx expr) {
		assert(type.equals(expr.type));
		super.add(expr);
		exprList.addAll(expr.exprList);
	}
	
	public void addAll(Collection<Expr> args) {
		exprList.addAll(args);
	}
	
	@Override
	public String toString() {
		return getExpr().toString();
	}
	
	
}
