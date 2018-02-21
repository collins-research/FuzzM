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

import jkind.lustre.Expr;
import jkind.lustre.IdExpr;
import jkind.lustre.UnaryExpr;
import jkind.lustre.UnaryOp;
import jkind.lustre.visitors.ExprIterVisitor;

public class StepDependency extends ExprIterVisitor {
	
	private Set<String> depSet;
	private PreDependency preVisitor;
	
	private StepDependency() {
		preVisitor = new PreDependency(); 
		depSet = new HashSet<>();
	}
	
	public Set<String> getDepSet() {
		return depSet;
	}
	
	public Set<String> getPreSet() {
		return preVisitor.getPreSet();
	}
	
	public static StepDependency computeDependencies(Expr e) {
		StepDependency stepVisitor = new StepDependency();
		e.accept(stepVisitor);
		return stepVisitor;
	}
	
	@Override
	public Void visit(IdExpr e) {
		depSet.add(e.id);
		return null;
	}
	
	@Override
	public Void visit(UnaryExpr e) {
		if (e.op.equals(UnaryOp.PRE)) {
			e.expr.accept(preVisitor);
		} else {
			super.visit(e);
		}
		return null;
	}
	
}
