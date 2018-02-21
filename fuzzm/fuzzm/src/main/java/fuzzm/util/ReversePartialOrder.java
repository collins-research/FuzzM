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

/**
 * An extension of PartialOrder that iterates from largest to
 * smallest.
 *
 * @param <T>
 */
public class ReversePartialOrder<T> extends PartialOrder<T> {
	@Override
	public Iterator<T> iterator() {
		// This will iterate top down.
		return totalOrder().iterator();
	}

}