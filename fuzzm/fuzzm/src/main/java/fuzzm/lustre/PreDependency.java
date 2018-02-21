/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.lustre;

import java.util.HashSet;
import java.util.Set;

import jkind.lustre.BinaryExpr;
import jkind.lustre.BinaryOp;
import jkind.lustre.Expr;
import jkind.lustre.IdExpr;
import jkind.lustre.UnaryExpr;
import jkind.lustre.UnaryOp;
import jkind.lustre.visitors.ExprIterVisitor;

public class PreDependency extends ExprIterVisitor {
	
	private Set<String> preSet;
	
	protected PreDependency() {
		preSet = new HashSet<>();
	}

	static PreDependency computeDependencies(Expr e) {
		PreDependency initVisitor = new PreDependency();
		e.accept(initVisitor);
		return initVisitor;
	}
	
	Set<String> getPreSet() {
		return preSet;
	}
	
	@Override
	public Void visit(IdExpr e) {
		preSet.add(e.id);
		return null;
	}
	
	@Override
	public Void visit(UnaryExpr e) {
		if (e.op.equals(UnaryOp.PRE)) {
			assert(false);
		}
		super.visit(e);
		return null;
	}
	
	@Override
	public Void visit(BinaryExpr e) {
		if (e.op.equals(BinaryOp.ARROW)) {
			e.right.accept(this);
		} else {
			e.left.accept(this);
			e.right.accept(this);
		}
		return null;
	}
	

}
