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

import fuzzm.util.Copy;
import fuzzm.util.IntervalVector;
import fuzzm.util.Rat;
import fuzzm.util.RatVect;
import fuzzm.util.TypedName;
import fuzzm.util.Vector;
import jkind.lustre.BinaryExpr;
import jkind.lustre.BinaryOp;
import jkind.lustre.Expr;
import jkind.lustre.NamedType;
import jkind.lustre.RealExpr;
import jkind.util.BigFraction;

public class ExprVect extends Vector<Expr> implements Copy<ExprVect> {

	private static final long serialVersionUID = 9058509602605173261L;

	public ExprVect() {
		super();
	}
	
	public ExprVect(ExprVect arg) {
		super();
		for (TypedName key: arg.keySet()) {
			put(key,arg.get(key));
		}
	}
	
	public ExprVect(RatVect v) {
		super();
		for (TypedName key: v.keySet()) {
			put(key,Rat.toExpr(v.get(key)));
		}
	}
	
	public ExprVect(IntervalVector v) {
		super();
		for (TypedName key: v.keySet()) {
			put(key,Rat.cast(key.name,key.type));
		}
	}

	private static boolean isZero(Expr term) {
		if (term instanceof RealExpr) {
			BigDecimal value = ((RealExpr) term).value;
			return (value.signum() == 0);
		}
		return false;
	}
	
	public ACExprCtx dot(Vector<Expr> x) {
		ACExprCtx acc = new ACExprCtx(NamedType.REAL,BinaryOp.PLUS);
		for (TypedName key: keySet()) {
			Expr left = get(key);
			Expr right = x.get(key);
			if (! (isZero(left) || isZero(right))) {
				acc.add(new BinaryExpr(get(key),BinaryOp.MULTIPLY,x.get(key)));
			}
		}
		return acc;
	}

	@Override
	public ExprVect mul(BigFraction M) {
		ExprVect res = new ExprVect();
		for (TypedName key: keySet()) {
			res.put(key,new BinaryExpr(get(key),BinaryOp.MULTIPLY,Rat.toExpr(M)));
		}
		return res;
	}

	@Override
	public ExprVect add(Vector<Expr> x) {
		ExprVect res = new ExprVect();
		for (TypedName key: keySet()) {
			res.put(key,new BinaryExpr(get(key),BinaryOp.PLUS,x.get(key)));
		}
		return res;
	}

	@Override
	public ExprVect sub(Vector<Expr> x) {
		ExprVect res = new ExprVect();
		for (TypedName key: keySet()) {
			res.put(key,new BinaryExpr(get(key),BinaryOp.MINUS,x.get(key)));
		}
		return res;
	}

	@Override
	public Expr get(TypedName key) {
		if (containsKey(key)) {
			return super.get(key);
		}
		// NOTE: we assume that the only place we would do this is
		// in the context of, say, a dot product computation where
		// the values are rational.
		return new RealExpr(BigDecimal.ZERO);
	}

	@Override
	public ExprVect copy() {
		return new ExprVect(this);
	}
	
}
