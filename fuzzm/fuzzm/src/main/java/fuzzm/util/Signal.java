/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.util;

import java.util.ArrayList;

public abstract class Signal<V extends Copy<V>> extends ArrayList<V> {

	private static final long serialVersionUID = 1L;
	
	public Signal(Signal<V> x) {
		super();
		for (V v: x) {
			add(v.copy());
		}
	}
	
	public Signal() {
		super();
	}

	public int bytes() {
		int res = 0;
		for (V v: this) {
			res += v.bytes();
		}
		return res;
	}
	
}
