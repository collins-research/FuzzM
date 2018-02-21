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

import fuzzm.value.poly.PolyEvaluatableValue;
import jkind.lustre.NamedType;

public class PolyFunctionLookup {

	final FunctionSignature sigs;
	final FunctionLookup<PolyEvaluatableValue> values;
	final FunctionLookup<List<PolyEvaluatableValue>> args;

	public PolyFunctionLookup(FunctionSignature fns) {
		sigs = fns;
		values = new FunctionLookup<>(fns.keySet());
		args = new FunctionLookup<>(fns.keySet());
	}
	
	public PolyFunctionLookup(FunctionSignature sigs, FunctionLookup<PolyEvaluatableValue> values, FunctionLookup<List<PolyEvaluatableValue>> args) {
		this.sigs   = sigs;
		this.values = values;
		this.args   = args;
	}
	
	public List<NamedType> getArgTypes(String function) {
		return sigs.getArgTypes(function);
	}
	
	public NamedType getFnType(String function) {
		return sigs.getFnType(function);
	}	

	public PolyEvaluatableValue getFnValue(String function, EvaluatableArgList args) {
		return values.get(function, args);
	}
	
	public void setFnValue(String function, EvaluatableArgList args, PolyEvaluatableValue value) {
		values.set(function, args, value);
	}
	
	public List<PolyEvaluatableValue> getArgValues(String function, EvaluatableArgList args) {
		return this.args.get(function, args);
	}
	
	public void setArgValues(String function, EvaluatableArgList args, List<PolyEvaluatableValue> argv) {
		this.args.set(function, args, argv);
	}
	
	public List<PolyEvaluatableValue> getFnNthArgs(String function, int index) {
		Collection<List<PolyEvaluatableValue>> z = args.getValues(function);
		List<PolyEvaluatableValue> res = new ArrayList<>();
		for (List<PolyEvaluatableValue> arg: z) {
			res.add(arg.get(index));
		}
		return res;
	}
	
	public List<PolyEvaluatableValue> getFnValues(String function) {
		return new ArrayList<>(values.getValues(function));
	}
	
	@Override
	public String toString() {
		String res = sigs.toString() + "\n";
		res += "Function Value Polys:\n\n";
		res += values.toString() + "\n";
		res += "Function Argument Polys:\n\n";
		res += args.toString() + "\n";
		return res;
	}
	
}
