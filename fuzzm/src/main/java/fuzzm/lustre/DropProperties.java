package jfuzz.lustre;

import jkind.lustre.Node;
import jkind.lustre.Program;
import jkind.lustre.builders.NodeBuilder;
import jkind.lustre.visitors.AstMapVisitor;

public class DropProperties extends AstMapVisitor {
	
	public static Program drop(Program program) {
		return new DropProperties().visit(program);
	}

	@Override
	public Node visit(Node node) {
		NodeBuilder nb = new NodeBuilder(node);
		nb.clearProperties();
		return nb.build();
	}
}
