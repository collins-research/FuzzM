/* 
 * Copyright (C) 2018, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.lustre;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;

import jkind.lustre.BinaryExpr;
import jkind.lustre.BinaryOp;
import jkind.lustre.EnumType;
import jkind.lustre.Expr;
import jkind.lustre.IdExpr;
import jkind.lustre.IntExpr;
import jkind.lustre.NamedType;
import jkind.lustre.Node;
import jkind.lustre.Program;
import jkind.lustre.SubrangeIntType;
import jkind.lustre.VarDecl;
import jkind.lustre.builders.NodeBuilder;
import jkind.lustre.visitors.AstMapVisitor;

public class RemoveEnumTypes extends AstMapVisitor {
    
	public static Program program(Program program) {
		return new RemoveEnumTypes().visit(program);
	}

	static Collection<Expr> typeConstraints;
	@Override
	public Node visit(Node e) {
	    typeConstraints = new ArrayList<Expr>();
	    Node newNode = super.visit(e);
	    NodeBuilder b = new NodeBuilder(newNode);
	    b.addAssertions(typeConstraints);
	    Node res = b.build();
	    typeConstraints = null;
        return res;
	}
	
	private static Expr newConstraint(String name, BigInteger low, BigInteger high) {
	    Expr var = new IdExpr(name);
	    Expr upper = new IntExpr(high);
	    Expr lower = new IntExpr(low);
	    Expr lb = new BinaryExpr(lower,BinaryOp.LESSEQUAL,var);
	    Expr ub = new BinaryExpr(var,BinaryOp.LESSEQUAL,upper);
	    return new BinaryExpr(lb,BinaryOp.AND,ub);
	}
	
	@Override
	public VarDecl visit(VarDecl e) {
		if (e.type instanceof EnumType) {
		    EnumType et = (EnumType) e.type;
		    BigInteger low  = BigInteger.ZERO;
            BigInteger high = BigInteger.valueOf(et.values.size() - 1);
		    Expr constraint = newConstraint(e.id,low,high);
		    typeConstraints.add(constraint);
			return new VarDecl(e.id, NamedType.INT);
		} else if (e.type instanceof SubrangeIntType) {
	            SubrangeIntType sit = (SubrangeIntType) e.type;
	            BigInteger low  = sit.low;
	            BigInteger high = sit.high;
	            Expr constraint = newConstraint(e.id,low,high);
	            typeConstraints.add(constraint);
	            return new VarDecl(e.id, NamedType.INT);
	    } else {
	        return e;
		}
	}
}
