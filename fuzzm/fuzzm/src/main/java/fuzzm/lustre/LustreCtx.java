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

import jkind.lustre.Equation;
import jkind.lustre.Expr;
import jkind.lustre.IdExpr;
import jkind.lustre.NamedType;
import jkind.lustre.VarDecl;

public class LustreCtx {

	public Collection<Equation>  eqs;
	public Collection<VarDecl> decls;
	
	public LustreCtx() {
		eqs = new ArrayList<>();
		decls = new ArrayList<>();
	}
	
	public LustreCtx(LustreCtx arg) {
		this.eqs  = new ArrayList<>(arg.eqs);
		this.decls = new ArrayList<>(arg.decls);
	}
	
	public IdExpr define(String name, NamedType type, Expr body) {
		IdExpr   stepID = new IdExpr(name);
		eqs.add(new Equation(stepID,body));
		decls.add(new VarDecl(name,type));		
		return stepID;
	}
	
	public void add(LustreCtx arg) {
		eqs.addAll(arg.eqs);
		decls.addAll(arg.decls);
	}
	
}
