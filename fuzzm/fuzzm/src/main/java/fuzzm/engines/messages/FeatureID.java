/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.engines.messages;

/**
 * The constraint ID ties the various messages back to
 * a specific feature (and its polarity).
 *
 */
public class FeatureID {
	public int constraintID;
	public boolean objective;
	public FeatureID(int constraintID, boolean objective) {
		this.constraintID = constraintID;
		this.objective = objective;
	}

	@Override
	public String toString() {
		return "id:" + (objective ? "+" : "-") + Integer.toString(constraintID);
	}
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + constraintID;
		result = prime * result + (objective ? 0 : 1);
		return result;
	}
	
	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (!(obj instanceof FeatureID)) {
			return false;
		}
		FeatureID other = (FeatureID) obj;
		if (constraintID != other.constraintID) {
			return false;
		}
		if ( objective != other.objective) {
			return false;
		}
		return true;
	}
}
