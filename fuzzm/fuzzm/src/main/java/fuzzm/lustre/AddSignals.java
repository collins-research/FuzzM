/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.lustre;

import java.util.List;

import fuzzm.util.FuzzmName;
import fuzzm.util.IDString;
import jkind.lustre.BinaryExpr;
import jkind.lustre.BinaryOp;
import jkind.lustre.Equation;
import jkind.lustre.Expr;
import jkind.lustre.IdExpr;
import jkind.lustre.IntExpr;
import jkind.lustre.NamedType;
import jkind.lustre.Node;
import jkind.lustre.Program;
import jkind.lustre.UnaryExpr;
import jkind.lustre.UnaryOp;
import jkind.lustre.VarDecl;
import jkind.lustre.builders.NodeBuilder;

public class AddSignals {
	
	public static Program addTime(Program program) {
		MainBuilder mb = new MainBuilder(program);
		Node node = program.getMainNode();
		node = add_time_to_main(node);
		mb.updateMainNode(node);
		return mb.build();
	}
	
//	public static Program add_done(Program program, String done) {
//		MainBuilder mb = new MainBuilder(program);
//		Node main = program.getMainNode();
//		//if (containsDone(main,done)) {
//		//	System.out.println(ID.location() + "Linking in Done signal");
//		//	main = link_done_in_main(main,done);
//		//} else {
//			//if (done.equals(FuzzMSettings.doneName_default)) {
//			//	System.out.println(ID.location() + "Warning: Assuming always DONE");
//		main = add_done_to_main(main);
//			//} else {
//			//	throw new IllegalArgumentException("Specified DONE signal \"" + done + "\" not found among main model outputs");
//			//}
//		//}
//		mb.updateMainNode(main);
//		return mb.build();
//	}	
	
	public static boolean containsDone(Node main, String done) {
		List<VarDecl> z = main.outputs;
		for (VarDecl v: z) {
			if ((v.id.equals(done)) && (v.type == NamedType.BOOL)) {
				return true;
			}
		}
		return false;
	}
	
	private static Node add_time_to_main(Node node) {
		// _k = 0 -> ((pre _k) + 1);
		NodeBuilder nb = new NodeBuilder(node);
		IDString time = FuzzmName.time;
		nb.addOutput(new VarDecl(time.name(),NamedType.INT));
		IdExpr k = new IdExpr(time.name());
		Expr pre = new UnaryExpr(UnaryOp.PRE, k);
		Expr one = new IntExpr(1);
		Expr plus = new BinaryExpr(pre, BinaryOp.PLUS, one);
		Expr zero = new IntExpr(0);
		Expr rhs  = new BinaryExpr(zero,BinaryOp.ARROW,plus);
		nb.addEquation(new Equation(k,rhs));
		return nb.build();
	}
	
//	private static Node add_done_to_main(Node node) {
//		// Rather than one cycle, allow it to be anything ..
//		// _done = true -> false;
//		NodeBuilder nb = new NodeBuilder(node);
//		nb.addOutput(new VarDecl(FuzzmName.done,NamedType.BOOL));
//		IdExpr done = new IdExpr(FuzzmName.done);
//		Expr T = new BoolExpr(true);
//		//Expr F = new BoolExpr(false);
//		//Expr rhs  = new BinaryExpr(T,BinaryOp.ARROW,F);
//		nb.addEquation(new Equation(done,T));
//		return nb.build();
//	}
	
//	private static Node link_done_in_main(Node node, String done) {
//		// _done = done;
//		NodeBuilder nb = new NodeBuilder(node);
//		nb.addOutput(new VarDecl(FuzzMName.done,NamedType.BOOL));
//		IdExpr newDone = new IdExpr(FuzzMName.done);
//		IdExpr oldDone = new IdExpr(done);
//		nb.addEquation(new Equation(newDone,oldDone));
//		return nb.build();
//	}
	
}
