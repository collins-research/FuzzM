/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.lustre.indexed;

import jkind.lustre.visitors.ExprVisitor;

public interface IndexedExprVisitor<T> extends ExprVisitor<T> {
	public T visit(IndexedIdExpr e);
}
