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
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import jkind.lustre.Function;
import jkind.lustre.NamedType;
import jkind.lustre.VarDecl;

public class FunctionSignature {

	final private Map<String,List<NamedType>>           signatures;
	final private Map<String,NamedType>                 fout;
	
	private static List<NamedType> typeListFromVarDecl(List<VarDecl> args) {
		List<NamedType> res = new ArrayList<>();
		for (VarDecl vd: args) {
			res.add((NamedType) vd.type);
		}
		return res;		
	}
	
	public Collection<String> keySet() {
		return signatures.keySet();
	}
	
	public FunctionSignature(List<Function> flist) {
		signatures = new HashMap<>();
		fout = new HashMap<>();
		for (Function f: flist) {
		    assert(f.outputs.size() <= 1);
			signatures.put(f.id, typeListFromVarDecl(f.inputs));
			if (f.outputs.size() > 1) throw new IllegalArgumentException();
			fout.put(f.id,(NamedType) f.outputs.get(0).type);
		}
	}
	
	public List<NamedType> getArgTypes(String function) {
		List<NamedType> res = signatures.get(function);
		if (res == null) throw new IllegalArgumentException();
		return res;
	}
	
	public NamedType getFnType(String function) {
		return fout.get(function);
	}	

	@Override
	public String toString() {
		String res = "Function Signatures :\n\n";
		for (String fn: fout.keySet()) {
			String delimit = "";
			String args = "(";
			for (NamedType type: getArgTypes(fn)) {
				args += delimit + type;
				delimit = ",";
			}
			args += ")";
			res += fn + args + ":" + getFnType(fn) + "\n";
		}
		return res;
	}
	
}
