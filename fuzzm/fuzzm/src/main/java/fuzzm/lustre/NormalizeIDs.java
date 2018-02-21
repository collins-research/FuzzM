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
import java.util.List;

import fuzzm.util.ID;
import jkind.lustre.Equation;
import jkind.lustre.Expr;
import jkind.lustre.Function;
import jkind.lustre.FunctionCallExpr;
import jkind.lustre.IdExpr;
import jkind.lustre.Node;
import jkind.lustre.NodeCallExpr;
import jkind.lustre.Program;
import jkind.lustre.VarDecl;
import jkind.lustre.visitors.AstMapVisitor;

public class NormalizeIDs extends AstMapVisitor {

	public static Program normalize(Program program) {
		return new NormalizeIDs().visit(program);
	}
	
	@Override
	public Program visit(Program e) {
		Program x = super.visit(e);
		return new Program(x.location,x.types,x.constants,x.functions,x.nodes, ID.encodeString(x.main));
	}
	
	@Override
	public Equation visit(Equation e) {
		List<IdExpr> lhs = new ArrayList<IdExpr>();
		for (IdExpr id: e.lhs) {
			lhs.add((IdExpr) visit(id));
		}
		// Why can't I just visit(e.expr) ?
		Expr expr = e.expr.accept(this);
		return new Equation(e.location,lhs,expr);
	}

	@Override
	public Expr visit(IdExpr e) {
		String name = e.id;
		return new IdExpr(e.location,ID.encodeString(name));
	}

	@Override
	public VarDecl visit(VarDecl e) {
		String name = e.id;
		return new VarDecl(e.location,ID.encodeString(name), e.type);
	}
	
	@Override
	public NodeCallExpr visit(NodeCallExpr e) {
		NodeCallExpr x = (NodeCallExpr) super.visit(e);
		String name = x.node;
		return new NodeCallExpr(x.location,ID.encodeString(name),x.args);
	}
	
	@Override
	public FunctionCallExpr visit(FunctionCallExpr e) {
		FunctionCallExpr x = (FunctionCallExpr) super.visit(e);
		String name = x.function;
		return new FunctionCallExpr(x.location,ID.encodeString(name),x.args);
	}
	
	@Override
	public Node visit(Node e) {
		Node x = super.visit(e);
		String name = x.id;
		return new Node(x.location,
						ID.encodeString(name),
						x.inputs,
						x.outputs,
						x.locals,
						x.equations,
						x.properties,
						x.assertions,
						x.realizabilityInputs,
						x.contract,
						x.ivc);
	}

	@Override
	public Function visit(Function e) {
		Function x = super.visit(e);
		String name = x.id;
		return new Function(x.location,
							ID.encodeString(name),
							x.inputs,
							x.outputs);
	}

	@Override
	protected List<String> visitProperties(List<String> es) {
		List<String> res = new ArrayList<String>();
		for (String s: es) {
			res.add(ID.encodeString(s));
		}
		return res;
	}
}