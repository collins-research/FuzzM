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
	public RestrictionResult andTrue2(VariableEquality left);
	public RestrictionResult andTrue2(VariableInterval left);
	public RestrictionResult andTrue2(VariableLess     left);
	public RestrictionResult andTrue2(VariableGreater  left);
	public RestrictionResult andTrue2(VariableBoolean  left);
	public RestrictionResult andTrue2(VariablePhantom  left);
    public Variable minSet(Variable right);
    public Variable minSet2(VariableEquality left);
    public Variable minSet2(VariableInterval left);
    public Variable minSet2(VariableLess     left);
    public Variable minSet2(VariableGreater  left);
    public Variable minSet2(VariableBoolean  left);
    public Variable minSet2(VariablePhantom  left);    
    public Variable maxSet(Variable right);
    public Variable maxSet2(VariableEquality left);
    public Variable maxSet2(VariableInterval left);
    public Variable maxSet2(VariableLess     left);
    public Variable maxSet2(VariableGreater  left);
    public Variable maxSet2(VariableBoolean  left);
    public Variable maxSet2(VariablePhantom  left);
    public Variable target (boolean trueL, Variable right);
    public Variable target2(boolean trueL, VariableEquality left);
    public Variable target2(boolean trueL, VariableInterval left);
    public Variable target2(boolean trueL, VariableLess     left);
    public Variable target2(boolean trueL, VariableGreater  left);
    public Variable target2(boolean trueL, VariableBoolean  left);
	public Variable target2(boolean trueL, VariablePhantom  left);
}
