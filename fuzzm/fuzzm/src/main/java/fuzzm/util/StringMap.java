/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.util;

import java.util.HashMap;
import java.util.Map;

public class StringMap<V> extends HashMap<String,V> {

	private static final long serialVersionUID = 2558872466324889478L;

	public StringMap(Map<String, V> arg) {
		super(arg);
	}

	public StringMap() {
		super();
	}

	@Override
	public boolean containsKey(Object arg) {
		throw new IllegalArgumentException();
	}
	
	public boolean containsKey(String arg) {
		return super.containsKey(arg);
	}
	
	@Override
	public V get(Object arg) {
		throw new IllegalArgumentException();
	}
	
	public V get(String arg) {
		return super.get(arg);
	}
		
}
