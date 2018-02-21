/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.value.poly;

import java.util.HashMap;
import java.util.Map;
import java.util.Random;

import fuzzm.poly.AbstractPoly;
import fuzzm.poly.PolyBool;
import fuzzm.poly.VariableID;
import fuzzm.util.Debug;
import fuzzm.util.ID;

public class GlobalState {
	
	private static Map<VariableID,AbstractPoly> rewrite = new HashMap<>();
	private static PolyBool invariants = PolyBool.TRUE;
	private static Random oracle = new Random();
	
	public static Random oracle() {
		return oracle;
	}
	
	private static long next_sequence = 0;
	private static final Object seq_lock = new Object();
	public static long next_sequence_id () {
		synchronized (seq_lock) {
			return next_sequence++;
		}
	}

	public static void addRewrite(VariableID v, AbstractPoly p) {
		assert(Thread.holdsLock(GlobalState.class));
		rewrite.put(v, p);
	}

	public static Map<VariableID,AbstractPoly> getRewrites() {
		assert(Thread.holdsLock(GlobalState.class));
		return rewrite;
	}
	
	public static void addConstraint(PolyBool c) {
		assert(Thread.holdsLock(GlobalState.class));
		if (Debug.logic()) System.out.println(ID.location() + "Adding Constraint : " + c);
		invariants = invariants.and(c);
		if (Debug.logic()) System.out.println(ID.location() + "Updated Constraint : " + invariants);
	}

	public static PolyBool getInvariants() {
		assert(Thread.holdsLock(GlobalState.class));
		return invariants;
	}
	
	public static void clearGlobalState() {
		assert(Thread.holdsLock(GlobalState.class));
		VariableID.clearGlobalState();
		rewrite = new HashMap<>();
		invariants = PolyBool.TRUE;
	}

}
