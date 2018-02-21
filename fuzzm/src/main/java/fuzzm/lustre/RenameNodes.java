package jfuzz.lustre;

import java.util.Map;

import jkind.lustre.Node;
import jkind.lustre.Program;
import jkind.lustre.builders.NodeBuilder;
import jkind.lustre.visitors.AstMapVisitor;

public class RenameNodes extends AstMapVisitor {

	private Map<String,String> rw;
	
	private RenameNodes(Map<String,String> rw) {
		this.rw = rw;
	}
	
	public static Program rename(Program program, Map<String,String> rw) {
		RenameNodes res = new RenameNodes(rw);
		return res.visit(program);
	}

	@Override
	public Node visit(Node node) {
		if (rw.containsKey(node.id)) {
			NodeBuilder NodeB = new NodeBuilder(node);
			NodeB.setId(rw.get(node.id));
			Node z = NodeB.build();
			return z;
		}
		return node;
	}
}
