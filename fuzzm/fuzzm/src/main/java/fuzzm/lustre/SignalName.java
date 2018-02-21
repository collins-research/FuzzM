/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.lustre;

import fuzzm.util.ID;
import fuzzm.util.TypedName;

public class SignalName {
	
	public final TypedName name;
	public final int    time;

	public SignalName(TypedName name, int time) {
		this.name = name;
		this.time = time;
	}
	
	@Override
	public String toString() {
		String res = ID.decodeString(name.name);
		res = (time <= 0) ? res : res + "[" + time + "]";
		return res;
	}
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((name == null) ? 0 : name.hashCode());
		result = prime * result + time;
		return result;
	}
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (! (obj instanceof SignalName))
			return false;
		SignalName other = (SignalName) obj;
		if (!name.equals(other.name))
			return false;
		if (time != other.time)
			return false;
		return true;
	}
}
