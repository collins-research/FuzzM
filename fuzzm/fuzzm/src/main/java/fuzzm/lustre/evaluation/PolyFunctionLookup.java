/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.lustre.evaluation;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import fuzzm.poly.VariableID;
import fuzzm.value.poly.BooleanPoly;
import fuzzm.value.poly.IntegerPoly;
import fuzzm.value.poly.PolyEvaluatableValue;
import fuzzm.value.poly.RationalPoly;
import jkind.lustre.NamedType;

public class PolyFunctionLookup {

	final FunctionSignature sigs;
	final FunctionLookup<PolyEvaluatableValue> polyValues;
	final FunctionLookup<VariableID> varValues;
    final FunctionLookup<List<PolyEvaluatableValue>> polyArgs;
    final FunctionLookup<List<VariableID>> varArgs;

	public PolyFunctionLookup(FunctionSignature fns) {
		sigs = fns;
		polyValues = new FunctionLookup<>(fns.keySet());
		polyArgs = new FunctionLookup<>(fns.keySet());
        varValues = new FunctionLookup<>(fns.keySet());
        varArgs = new FunctionLookup<>(fns.keySet());
	}
	
//	public PolyFunctionLookup(FunctionSignature sigs, FunctionLookup<PolyEvaluatableValue> values, FunctionLookup<List<PolyEvaluatableValue>> args) {
//		this.sigs   = sigs;
//		this.values = values;
//		this.args   = args;
//	}
	static PolyEvaluatableValue toPEV(VariableID varid) {
	    if (varid.name.name.type == NamedType.BOOL) {
	        return(new BooleanPoly(varid));
	        // return (varid.cex.compareTo(BigFraction.ZERO) == 0) ? BooleanPoly.FALSE : BooleanPoly.TRUE;
	    }
	    if (varid.name.name.type == NamedType.INT) {
	        return new IntegerPoly(varid);
	    }
	    if (varid.name.name.type == NamedType.REAL) {
	        return new RationalPoly(varid);
	    }
	    throw new IllegalArgumentException();
	}
	    

	public List<NamedType> getArgTypes(String function) {
		return sigs.getArgTypes(function);
	}
	
	public NamedType getFnType(String function) {
		return sigs.getFnType(function);
	}	

	public PolyEvaluatableValue getFnPolyValue(String function, EvaluatableArgList args) {
		return polyValues.get(function, args);
	}
	
    public VariableID getFnVarValue(String function, EvaluatableArgList args) {
        return varValues.get(function, args);
    }
    
	public void setFnValue(String function, EvaluatableArgList args, VariableID value) {
        varValues.set(function, args, value);
        polyValues.set(function, args, toPEV(value));
	}
	
	public List<PolyEvaluatableValue> getArgPolyValues(String function, EvaluatableArgList args) {
		return this.polyArgs.get(function, args);
	}
	
    public List<VariableID> getArgVarValues(String function, EvaluatableArgList args) {
        return this.varArgs.get(function, args);
    }
    
	public void setArgValues(String function, EvaluatableArgList args, List<VariableID> argv) {
	    varArgs.set(function, args, argv);
	    List<PolyEvaluatableValue> pargv = new ArrayList<>();
	    for (VariableID v: argv) {
	        pargv.add(toPEV(v));
	    }
		this.polyArgs.set(function, args, pargv);
	}
	
	public List<PolyEvaluatableValue> getFnNthArgs(String function, int index) {
		Collection<List<PolyEvaluatableValue>> z = polyArgs.getValues(function);
		List<PolyEvaluatableValue> res = new ArrayList<>();
		for (List<PolyEvaluatableValue> arg: z) {
			res.add(arg.get(index));
		}
		return res;
	}
	
	public List<PolyEvaluatableValue> getFnValues(String function) {
		return new ArrayList<>(polyValues.getValues(function));
	}
	
	@Override
	public String toString() {
		String res = sigs.toString() + "\n";
		res += "Function Value Polys:\n\n";
		res += polyValues.toString() + "\n";
		res += "Function Argument Polys:\n\n";
		res += polyArgs.toString() + "\n";
		return res;
	}
	
}
