package jfuzz.lustre;

import java.util.ArrayList;
import java.util.List;

import jkind.lustre.Expr;
import jkind.lustre.IdExpr;
import jkind.lustre.NamedType;
import jkind.lustre.Node;
import jkind.lustre.VarDecl;

public class ExtractFeatures {
	
	public static List<Expr> extract(Node mainNode) {
		List<Expr> res = new ArrayList<Expr>();
		if (mainNode != null) {
			for (VarDecl v: mainNode.outputs) {
				if (v.type == NamedType.BOOL) {
					res.add(new IdExpr(v.id));
				}
			}
		}		
		return res;
	}

}
