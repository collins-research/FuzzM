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

import fuzzm.util.FuzzMName;
import jkind.lustre.BinaryExpr;
import jkind.lustre.BinaryOp;
import jkind.lustre.Expr;
import jkind.lustre.IdExpr;
import jkind.lustre.IfThenElseExpr;
import jkind.lustre.IntExpr;
import jkind.lustre.NamedType;

public class SignalCtx extends ExprCtx {

	private List<Expr> exprList = new ArrayList<>();
	private Expr time = new IdExpr(FuzzMName.time);
			
	public SignalCtx(NamedType type) {
		super(type, ExprCtx.defaultValue(type));
	}

	public void add(ExprCtx arg) {
		assert(type.equals(arg.type));
		super.add(arg);
		exprList.add(arg.getExpr());
	}

	// We assume that signals are added sequentially ..
	public void add(SignalCtx arg) {
		assert(type.equals(arg.type));
		super.add(arg);
		exprList.addAll(arg.exprList);
	}

	public void add(Expr arg) {
		exprList.add(arg);
	}
	
	public void add(Collection<Expr> arg) {
		exprList.addAll(arg);
	}
	
	public void setTime(Expr time) {
		this.time = time;
	}
	
	private static Expr alternation(Expr time, int pivot, Expr left, Expr right) {
		Expr test = new BinaryExpr(time,BinaryOp.LESSEQUAL,new IntExpr(pivot));
		return new IfThenElseExpr(test,left,right);
	}
	
	private Expr bindExprRec(int min, int max,int index, String base) {
		int span = max - min;
		if (span == 0) return exprList.get(min);
		if (span == 1) return alternation(time,min,exprList.get(min),exprList.get(max));
		int half = span/2;
		Expr left  = bindExprRec(min,min+half,index*2+1,base);
		Expr right = bindExprRec(min+half+1,max,index*2,base);
		Expr res = define(base + index,type,alternation(time,min+half,left,right));
		return res;
	}
	
	@Override
	public ExprCtx bind(String base) {
		int size = exprList.size();
		if (size <= 0) return new ExprCtx(super.bind(base));
		Expr lastExpr = bindExprRec(0,size-1,1,base);
		setExpr(lastExpr);
		return new ExprCtx(super.bind(base));		
	}

}
