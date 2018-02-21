/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.poly;

public interface VariableInterface {
	
	public RestrictionResult andTrue(Variable right);
	public RestrictionResult andTrue2(VariableEquality   left);
	public RestrictionResult andTrue2(VariableInterval     left);
	public RestrictionResult andTrue2(VariableLess       left);
	public RestrictionResult andTrue2(VariableGreater    left);
	public RestrictionResult andTrue2(VariableBoolean left);
	
	public Variable andFalse(Variable right);
	public Variable andFalse2(VariableEquality   left);
	public Variable andFalse2(VariableInterval     left);
	public Variable andFalse2(VariableLess       left);
	public Variable andFalse2(VariableGreater    left);
	public Variable andFalse2(VariableBoolean    left);

}
