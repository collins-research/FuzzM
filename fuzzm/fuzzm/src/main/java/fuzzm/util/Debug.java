/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.util;

public class Debug {

	private static boolean enabled = false;
	private static boolean proof   = false;

	public static boolean isEnabled() {
		return enabled;
	}

	public static boolean proof() {
		return proof;
	}

	public static void setEnabled(boolean enabled) {
		if ((! Debug.enabled) && enabled) System.out.println(ID.location(1) + "Enabling Debug ..");
		if (Debug.enabled && (! enabled)) System.out.println(ID.location(1) + "Disabling Debug.");
		Debug.enabled = enabled;
	}

	public static void setProof(boolean enabled) {
		if ((! Debug.proof) && enabled) System.out.println(ID.location(1) + "Enabling Logic ..");
		if (Debug.proof && (! enabled)) System.out.println(ID.location(1) + "Disabling Logic.");
		Debug.proof = enabled;
	}
}
