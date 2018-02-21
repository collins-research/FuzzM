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

import jkind.lustre.Node;
import jkind.lustre.Program;
import jkind.lustre.builders.ProgramBuilder;

public class MainBuilder extends ProgramBuilder {

	Node mainNode;
	String mainName;
	List<Node> nodeList;
	
	public MainBuilder(Program program) {
		super(program);
		mainName = program.main;
		mainNode = program.getMainNode();
		nodeList = program.nodes;
	}

	public MainBuilder updateMainNode(Node node) {
		mainNode = node;
		return this;
	}
	
	@Override
	public Program build() {
		List<Node> res = new ArrayList<Node>();
		for (Node node: nodeList) {
			if (node.id.equals(mainName)) {
				res.add(mainNode);
			} else {
				res.add(node);
			}			
		}
		clearNodes();
		addNodes(res);
		return super.build();
	}
	
}
