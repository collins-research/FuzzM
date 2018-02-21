package jfuzz.util;

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