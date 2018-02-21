package jfuzz.lustre.indexed;

import jkind.lustre.Type;
import jkind.lustre.VarDecl;

public class IndexedVarDecl extends VarDecl {
	public int index;
	public IndexedVarDecl(VarDecl x, int index) {
		super(x.location,x.id,x.type);
		this.index = index;
	}
	public IndexedVarDecl(String id, Type type, int index) {
		super(id,type);
		this.index = index;
	}

}
