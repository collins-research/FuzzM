package jfuzz.lustre;

import java.util.ArrayList;
import java.util.List;

import jkind.lustre.Expr;
import jkind.lustre.IdExpr;
import jkind.lustre.Node;
import jkind.lustre.Program;
import jkind.lustre.visitors.AstIterVisitor;

public class ExtractProperties extends AstIterVisitor {

	private String mainName;
	private List<Expr> properties;

	private ExtractProperties(String mainName, List<Expr> properties) {
		this.mainName = mainName;
		this.properties = properties;
	}
	
	public static List<Expr> mainProperties(String mainName, Program program) {
		ExtractProperties res = new ExtractProperties(mainName,new ArrayList<Expr>());
		res.visit(program);
		return res.properties;
	}

	@Override
	public Void visit(Node node) {
		if (node.id.equals(mainName)) {
			List<String> oldprops = node.properties;
			for (String s: oldprops) {
				properties.add(new IdExpr(s));
			}
		}
		return null;
	}

}

