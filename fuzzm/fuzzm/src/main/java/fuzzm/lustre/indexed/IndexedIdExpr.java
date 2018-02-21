/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.lustre.indexed;

import jkind.lustre.IdExpr;

public class IndexedIdExpr extends IdExpr {
	public int index;
	public IndexedIdExpr(IdExpr x, int index) {
		super(x.location,x.id);
		this.index = index;
	}
	public IndexedIdExpr(String id, int index) {
		super(id);
		this.index = index;
	}
	public <T> T accept(IndexedExprVisitor<T> visitor) {
		return visitor.visit(this);
	}
	public String toString() {
		return super.toString() + "<" + index + ">";
	}
}
