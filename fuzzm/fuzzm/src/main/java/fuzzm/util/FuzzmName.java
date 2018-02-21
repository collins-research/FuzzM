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
	public static final String fuzzProperty   = "__fuzzProperty";
	public static final String time           = "__time";
	public static final String boundingBox    = "__boundingBox_";
	public static final String pivotDot       = "__pivotDot_";
	public static final String region         = "__region_";
	public static final String assertion      = "__assertion_";
	public static final String exprCtxName    = "_exprCtxName_";
    public static final String polyConstraint = "__poly_constraint";
    public static final String polyEval       = "__poly_eval";
    public static final String polyTerm       = "__poly_term";
}
