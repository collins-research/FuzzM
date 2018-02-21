/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.poly;

public class OpType {
	
	final String name;
	public static final OpType AND = new OpType("and");
	public static final OpType OR  = new OpType("or");

	protected OpType(String name) {
		this.name = name;
	}

	public OpType not() {
		return ((this == AND) ? OR : AND);
	}
	
	public boolean op(boolean x, boolean y) {
		return (this == OR) ? x | y : x & y;
	}
}
