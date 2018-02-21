/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.lustre;

import fuzzm.util.ID;
import fuzzm.util.FuzzMName;
import jkind.lustre.Equation;
import jkind.lustre.IdExpr;
import jkind.lustre.Location;
import jkind.lustre.NamedType;
import jkind.lustre.Node;
import jkind.lustre.Program;
import jkind.lustre.VarDecl;
import jkind.lustre.builders.NodeBuilder;

public class FuzzProgram {

	public static Program fuzz(Program program, BooleanCtx constraint) {
		Node main = program.getMainNode();
		main = fuzz(main,constraint);
		MainBuilder mb = new MainBuilder(program);
		mb.updateMainNode(main);
		return mb.build();
	}

	private static Node fuzz(Node node, ExprCtx constraint) {
		NodeBuilder NodeB = new NodeBuilder(node);
		NodeB = NodeB.clearProperties();
		String pname = FuzzMName.fuzzProperty;
		NodeB = NodeB.addLocal(new VarDecl(Location.NULL,pname,NamedType.BOOL));
		NodeB = NodeB.addEquations(constraint.eqs);
		NodeB = NodeB.addLocals(constraint.decls);
		System.out.println(ID.location() + "Constraint: " + constraint.getExpr());
		NodeB = NodeB.addEquation(new Equation(new IdExpr(pname),constraint.getExpr()));
		NodeB = NodeB.addProperty(pname);
		Node z = NodeB.build();
		return z;
	}

}
