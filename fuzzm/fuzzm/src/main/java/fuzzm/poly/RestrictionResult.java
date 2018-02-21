/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.poly;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

public class RestrictionResult {
	
	public Variable newConstraint;
	List<Variable> restrictionList;
	
	public RestrictionResult(Variable newConstraint) {
		this.newConstraint = newConstraint;
		this.restrictionList = new ArrayList<>();
	}

	public RestrictionResult(Variable newConstraint, Variable newRestriction) {
		this(newConstraint);
		this.restrictionList.add(newRestriction);
	}

	public RestrictionResult(Variable newConstraint, List<Variable> restrictionList) {
		this.newConstraint = newConstraint;
		this.restrictionList = restrictionList;
	}

	public static RestrictionResult restrictionInterval(RestrictionResult gt, RestrictionResult lt) {
		VariableInterval r = new VariableInterval((VariableGreater) gt.newConstraint ,(VariableLess) lt.newConstraint);
		List<Variable> rlst = new ArrayList<>(gt.restrictionList);
		rlst.addAll(lt.restrictionList);
		return new RestrictionResult(r,rlst);
	}
	
	public String toString() {
		return newConstraint.toString() + " & " + Arrays.toString(restrictionList.toArray());
	}
	
	public String toACL2() {
		String res = newConstraint.toACL2() + "(and ";
		for (Variable v: restrictionList) {
			res += " " + v.toACL2();
		}
		res += ")";
		return "(and " + res + ")";
	}
	
}
