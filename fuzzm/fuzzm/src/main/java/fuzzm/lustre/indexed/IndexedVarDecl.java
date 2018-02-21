/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.lustre.indexed;

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
