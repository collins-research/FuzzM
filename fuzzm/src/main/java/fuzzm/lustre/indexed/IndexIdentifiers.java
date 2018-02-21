package jfuzz.lustre.indexed;

import java.util.Map;

import jkind.lustre.Expr;
import jkind.lustre.IdExpr;
import jkind.lustre.Node;
import jkind.lustre.VarDecl;

public class IndexIdentifiers extends IndexedAstMapVisitor {

	private Map<String,Integer> nameToIndex;
	
	private IndexIdentifiers(Map<String,Integer> nameToIndex) {
		this.nameToIndex = nameToIndex;
	}
	
	public static Node indexIdentifiers(Node node, Map<String,Integer> nameToIndex) {
		IndexIdentifiers res = new IndexIdentifiers(nameToIndex);
		return (Node) node.accept(res);
	}

	public Expr visit(IdExpr e) {
		String name = e.id;
		Integer index = nameToIndex.get(name);
		if (index == null) System.out.println("IndexIdentifer Missing Name : " + name);
		assert(index != null);
		return new IndexedIdExpr((IdExpr) e,index);
	}

	public IndexedVarDecl visit(VarDecl e) {
		String name = e.id;
		Integer index = nameToIndex.get(name);
		if (index == null) System.out.println("IndexIdentifer Missing Name : " + name);
		assert(index != null);
		return new IndexedVarDecl((VarDecl) e,index);
	}
	
}
