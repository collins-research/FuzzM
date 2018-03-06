/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.util;

/**
 * FuzzMName enumerates the special variable names used
 * at various points by FuzzM.
 *
 */
public class FuzzmName {
	public static final IDString fuzzProperty   = IDString.newID("fuzzProperty");
	public static final IDString time           = IDString.newID("time");
	public static final IDString pivotDot       = IDString.newID("pivotDot");
	public static final String   polyConstraint = "poly_constraint";
    public static final String   polyEval       = "poly_eval";
    public static final String   polyTerm       = "poly_term";
}
