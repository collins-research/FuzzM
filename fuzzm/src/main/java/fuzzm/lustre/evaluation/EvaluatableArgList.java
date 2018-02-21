package jfuzz.lustre.evaluation;

import java.util.ArrayList;

import jfuzz.value.hierarchy.EvaluatableValue;

public class EvaluatableArgList extends ArrayList<EvaluatableValue> {

	private static final long serialVersionUID = 7204007336721147321L;

	@Override
	public String toString() {
		String res = "(";
		String delimit = "";
		for (int index = 0; index<size(); index++) {
			res += delimit + get(index);
			delimit = ",";
		}
		return res + ")";
	}
	
}
