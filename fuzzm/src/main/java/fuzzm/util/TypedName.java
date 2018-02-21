package jfuzz.util;

import jkind.lustre.NamedType;

public class TypedName {

	public final String name;
	public final NamedType type;

	public TypedName(String name, NamedType type) {
		this.name = name.intern();
		this.type = type;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((name == null) ? 0 : name.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (! (obj instanceof TypedName))
			return false;
		TypedName other = (TypedName) obj;
		return name == other.name;
	}
	
	@Override
	public String toString() {
		return name;
	}
	
}
