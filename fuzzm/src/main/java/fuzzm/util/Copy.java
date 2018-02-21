package jfuzz.util;

public interface Copy<V> {
	V copy();
	int bytes();
}
