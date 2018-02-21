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

import fuzzm.util.PartialOrder;
import jkind.lustre.Node;
import jkind.lustre.NodeCallExpr;
import jkind.lustre.Program;
import jkind.lustre.visitors.AstIterVisitor;

public class OrderNodes extends AstIterVisitor {

	private PartialOrder<String> order;
	private Set<String> body;
	
	private OrderNodes() {
		body = null;
		order = new PartialOrder<String>();		
	}
	
	public static PartialOrder<String> computeOrder(Program program) {
		OrderNodes res = new OrderNodes();
		res.visit(program);
		return res.order;
	}

	@Override
	public Void visit(NodeCallExpr call) {
		body.add(call.node);
		return null;
	}
	
	@Override
	public Void visit(Node node) {
		body = new HashSet<String>();
		super.visit(node);
		order.update(node.id,body);
		return null;
	}

}

