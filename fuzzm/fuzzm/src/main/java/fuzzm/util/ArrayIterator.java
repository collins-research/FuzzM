/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.util;

import java.util.Iterator;

public class ArrayIterator<T> implements Iterator<T> {
	private int next;
	private T[] array;

	public ArrayIterator(T[] array) {
		this.next = 0;
		this.array = array;
	}
	
	@Override
	public boolean hasNext() {
		return next < array.length;
	}
	
	@Override
	public T next() {
		return array[next++];
	}
	
}
