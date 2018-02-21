package jfuzz.util;

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
