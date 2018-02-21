/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.lustre.indexed;

import jkind.lustre.visitors.AstVisitor;

public interface IndexedASTVisitor<A,E extends A> extends AstVisitor<A,E> {
	public IndexedVarDecl visit(IndexedVarDecl e);
}
