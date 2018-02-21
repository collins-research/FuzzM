package jfuzz.lustre.evaluation;

import java.util.List;

import jfuzz.util.Rat;
import jfuzz.value.hierarchy.EvaluatableValue;
import jkind.lustre.NamedType;

public class FunctionLookupEV extends FunctionLookup<EvaluatableValue> {

	public FunctionSignature fsig;

	public FunctionLookupEV(FunctionSignature fsig) {
		super(fsig.keySet());
		this.fsig = fsig;
	}
	
	public List<NamedType> getArgTypes(String function) {
		return fsig.getArgTypes(function);
	}
	
	public NamedType getFnType(String function) {
		return fsig.getFnType(function);
	}	


	public void addEncodedString(String entry) {
		// String is of the form:
		// fname ftype tvalue [argtype argvalue]*
		String[] split = entry.split(" ");
		if (! (split.length >= 3 && (split.length % 2 == 1))) {
			throw new IllegalArgumentException("Expected string of the form 'fname ftype tvalue [argtype argvalue]*' but got: '" + entry + "'");
		}
		String fname = split[0];
		String ftype = split[1];
		String fvalue = split[2];
		EvaluatableValue evalue = Rat.ValueFromString(ftype, fvalue);
		EvaluatableArgList args = new EvaluatableArgList();
		for (int index=3;index<split.length;index+=2) {
			String argType  = split[index];
			String argValue = split[index+1];
			args.add(Rat.ValueFromString(argType, argValue));
		}
		set(fname,args,evalue);
	}

}
