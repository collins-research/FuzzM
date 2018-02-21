package jfuzz.poly;

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
		VariableInterval r = new VariableInterval((VariableGreater) gt.newConstraint ,(VariableLess) lt.newConstraint, OpType.AND);
		List<Variable> rlst = new ArrayList<>(gt.restrictionList);
		rlst.addAll(lt.restrictionList);
		return new RestrictionResult(r,rlst);
	}
	
	public String toString() {
		return newConstraint.toString() + " & " + Arrays.toString(restrictionList.toArray());
	}
	
	public String toACL2() {
		String res = newConstraint.toACL2();
		for (Variable v: restrictionList) {
			res = res + " " + v.toACL2();
		}
		return "(and " + res + ")";
	}
	
}
