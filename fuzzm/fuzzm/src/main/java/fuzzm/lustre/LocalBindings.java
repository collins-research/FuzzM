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

import jkind.lustre.BinaryExpr;
import jkind.lustre.BinaryOp;
import jkind.lustre.BoolExpr;
import jkind.lustre.Equation;
import jkind.lustre.Expr;
import jkind.lustre.Function;
import jkind.lustre.FunctionCallExpr;
import jkind.lustre.IdExpr;
import jkind.lustre.IfThenElseExpr;
import jkind.lustre.NamedType;
import jkind.lustre.Node;
import jkind.lustre.NodeCallExpr;
import jkind.lustre.Program;
import jkind.lustre.UnaryExpr;
import jkind.lustre.UnaryOp;
import jkind.lustre.VarDecl;
import jkind.lustre.builders.NodeBuilder;
import jkind.lustre.visitors.TypeAwareAstMapVisitor;

/**
 * 
 * Create new local bindings for:
 * - Expressions appearing in 'pre' operators.
 * - Arguments to node calls
 * 
 * We will also want
 * - Nested Boolean expressions (?)
 * - except 'not'
 * - If conditions
 * 
 * We will eventually be interested in variable
 * dependency (ie: x is a function of y and z)
 * 
 * Assumptions: variable names have been normalized.
 * 
 */
public class LocalBindings extends TypeAwareAstMapVisitor {

	public LocalBindings(List<Function> funcs) {
		super(funcs);
	}

	public static Program bindLocals(Program body) {
		return new LocalBindings(body.functions).visit(body);
	}

	private List<VarDecl> newLocals;
	private List<Equation> newEquations;
	private int counter = 0;
	private boolean arrowContext = false;
	
	private IdExpr getFreshId() {
		return new IdExpr("_" + counter++);
	}
	
	static boolean isID(Expr e) {
		// Presumably the Expr e is boolean ..
		if (e instanceof BoolExpr) {
			return true;
		}
		if (e instanceof IdExpr) {
			return true;
		}
		if (e instanceof UnaryExpr) {
			UnaryExpr x = (UnaryExpr) e;
			if (x.op.equals(UnaryOp.NOT)) {
				return isID(x.expr);
			}
		}
		return false;
	}
	
	// Ugh .. this isn't right.  I wonder if we even
	// had a problem before (?).  Specifically, I suspect
	// that we need to have more than boolean base cases.
	//
	// The problem we are trying to address is that
	// of lifting expressions out of arrow expressions.
	// Specifically, we don't want to introduce
	// unprotected (pre x) expressions.  Our solution
	// was to protect any expression pulled from the RHS
	// of an arrow expression with an arrow.  This also
	// serves to preserve the temporal properties of
	// the expression .. which may(?) be important ..
	// especially when combined with other signals.
	static Expr prefixExpr(boolean prefix, Expr e) {
		if (! prefix) return e;
		e = new BinaryExpr(new BoolExpr(false),BinaryOp.ARROW,e);
		return e;
	}
	
	void newEquation(IdExpr id, Expr expr) {
		newEquations.add(new Equation(id, prefixExpr(arrowContext,expr)));
	}
	
	public Expr visitNegativeAssertion(Expr e) {
		if (e instanceof BinaryExpr) {
			BinaryExpr bexpr = (BinaryExpr) e;
			BinaryOp op = bexpr.op;
			if (op.equals(BinaryOp.OR)) {
				return new BinaryExpr(visitNegativeAssertion(bexpr.left),op,visitNegativeAssertion(bexpr.right));
			}
			if (op.equals(BinaryOp.IMPLIES)) {
				return new BinaryExpr(visitPositiveAssertion(bexpr.left),op,visitNegativeAssertion(bexpr.right));
			}
		} else if (e instanceof UnaryExpr) {
			UnaryExpr uexpr = (UnaryExpr) e;
			UnaryOp op = uexpr.op;
			if (op.equals(UnaryOp.NOT)) {
				return new UnaryExpr(op,visitPositiveAssertion(uexpr.expr));
			}
		}
		return e.accept(this);
	}

	public Expr visitPositiveAssertion(Expr e) {
		//System.out.println(ID.location() + "Visiting Assertion : " + e.toString());
		if (e instanceof BinaryExpr) {
			BinaryExpr bexpr = (BinaryExpr) e;
			BinaryOp op = bexpr.op;
			if (op.equals(BinaryOp.AND)) {
				return new BinaryExpr(visitPositiveAssertion(bexpr.left),op,visitPositiveAssertion(bexpr.right));
			}
		} else if (e instanceof UnaryExpr) {
			UnaryExpr uexpr = (UnaryExpr) e;
			UnaryOp op = uexpr.op;
			if (op.equals(UnaryOp.NOT)) {
				return new UnaryExpr(op,visitNegativeAssertion(uexpr.expr));
			}
		}
		return e.accept(this);
	}

	@Override
	public List<Expr> visitAssertions(List<Expr> assertions) {
		ArrayList<Expr> res = new ArrayList<Expr>();
		for (Expr e: assertions) {
			res.add(visitPositiveAssertion(e));
		}
		return res;
	}
	
	@Override
	public Node visit(Node e) {
		newLocals = new ArrayList<>();
		newEquations = new ArrayList<>();
		counter = 0;
		NodeBuilder builder = new NodeBuilder(super.visit(e));
		builder.addLocals(newLocals);
		builder.addEquations(newEquations);
		return builder.build();
	}

	@Override
	public Expr visit(UnaryExpr e) {
		Expr expr = e.expr.accept(this);
		if ((! isID(expr)) && (e.op.equals(UnaryOp.PRE))) {
			IdExpr id = getFreshId();
			newLocals.add(new VarDecl(id.id, getType(e.expr)));
			newEquation(id,expr);
			return new UnaryExpr(e.op, id);
		}
		return new UnaryExpr(e.op, expr);
	}
	
	// Node calls are going to need to know .. 

	@Override
	public IfThenElseExpr visit(IfThenElseExpr e) {
		boolean isBool = (getType(e.elseExpr) == NamedType.BOOL);
		Expr res = super.visit(e);
		assert(res instanceof IfThenElseExpr);
		e = (IfThenElseExpr) res;
		Expr condE = e.cond;
		Expr thenE = e.thenExpr;
		Expr elseE = e.elseExpr;
		if (! isID(condE)) {
			IdExpr id = getFreshId();
			newLocals.add(new VarDecl(id.id, NamedType.BOOL));
			newEquation(id,condE);
			condE = id;
		}
		if (isBool) {
			if (! isID(thenE)) {
				IdExpr id = getFreshId();
				newLocals.add(new VarDecl(id.id, NamedType.BOOL));
				newEquation(id,thenE);
				thenE = id;
			}
			if (! isID(elseE)) {
				IdExpr id = getFreshId();
				newLocals.add(new VarDecl(id.id, NamedType.BOOL));
				newEquation(id,elseE);
				elseE = id;
			}
		}
		return new IfThenElseExpr(e.location,condE,thenE,elseE);
	}
	
	@Override
	public Expr visit(NodeCallExpr e) {
		//System.out.println(ID.location() + "Visiting Node Call : " + e.toString());
		Expr res = super.visit(e);
		assert(res instanceof NodeCallExpr);
		NodeCallExpr ex = ((NodeCallExpr) res);
		IdExpr id = getFreshId();
		newLocals.add(new VarDecl(id.id, getType(e)));
		newEquation(id,ex);
		return id;
	}
	
	@Override
	public Expr visit(FunctionCallExpr e) {
		//System.out.println(ID.location() + "Visiting Function Call : " + e.toString());
		Expr res = super.visit(e);
		assert(res instanceof FunctionCallExpr);
		e = ((FunctionCallExpr) res);
		IdExpr id = getFreshId();
		newLocals.add(new VarDecl(id.id, getType(e)));
		newEquation(id,e);
		return id;
	}
	
	@Override
	public Equation visit(Equation e) {
		Expr rhs = e.expr;
		if (rhs instanceof NodeCallExpr) {
			NodeCallExpr call = ((NodeCallExpr) rhs);
			List<Expr> args = new ArrayList<Expr>();
			for (Expr arg: call.args) {
				args.add(arg.accept(this));
			}
			call = new NodeCallExpr(rhs.location,call.node, args);		
			return new Equation(e.location,e.lhs,call);
		}
		if (rhs instanceof FunctionCallExpr) {
			FunctionCallExpr call = ((FunctionCallExpr) rhs);
			List<Expr> args = new ArrayList<Expr>();
			for (Expr arg: call.args) {
				args.add(arg.accept(this));
			}
			call = new FunctionCallExpr(rhs.location,call.function,args);
			return new Equation(e.location,e.lhs,call);
		}
		return super.visit(e);
	}
	
	@Override
	public Expr visit(BinaryExpr e) {
		Expr lhs = e.left.accept(this);
		Expr rhs = null;
		if (e.op.equals(BinaryOp.ARROW)) {
			boolean old_prefix = arrowContext;
			arrowContext = true;
			rhs = e.right.accept(this);
			arrowContext = old_prefix;
		} else {
			rhs = e.right.accept(this);
		}
		switch (e.op) {
		case EQUAL:
		case NOTEQUAL:
			if (getType(e.left) != NamedType.BOOL) {
				return new BinaryExpr(e.location,lhs,e.op, rhs);
			}
		case OR:
		case AND:
		case XOR:
		case IMPLIES:
			break;			
		default:
			return new BinaryExpr(e.location,lhs,e.op, rhs);
		}
		if (! isID(lhs)) {
			IdExpr id = getFreshId();
			newLocals.add(new VarDecl(id.id, NamedType.BOOL));
			newEquation(id,lhs);
			lhs = id;
		}
		if (! isID(rhs)) {
			IdExpr id = getFreshId();
			newLocals.add(new VarDecl(id.id, NamedType.BOOL));
			newEquation(id,rhs);
			rhs = id;
		}
		return new BinaryExpr(e.location,lhs,e.op,rhs);
	}
}
