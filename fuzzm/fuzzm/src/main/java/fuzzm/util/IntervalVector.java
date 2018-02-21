/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.util;

import java.util.ArrayList;
import java.util.List;

import fuzzm.lustre.ExprSignal;
import fuzzm.lustre.ExprVect;
import fuzzm.lustre.SignalName;
import jkind.util.BigFraction;

public class IntervalVector extends Vector<FuzzMInterval> implements Copy<IntervalVector> {

	private static final long serialVersionUID = 1991897878162721964L;
	
	public IntervalVector() {
		super();
	}
	
	public ExprVect getExprVector() {
		ExprVect res = new ExprVect();
		for (TypedName name: keySet()) {
			res.put(name,Rat.cast(name.name,get(name).type));
		}
		return res;
	}
	
	public ExprSignal getExprSignal(int k) {
		ExprVect v = getExprVector();
		ExprSignal res = new ExprSignal();
		for (int i=0;i<k;i++) {
			res.add(v);
		}
		return res;
	}
	
	public List<SignalName> elaborate(int k) {
		List<SignalName> res = new ArrayList<>();
		for (int i=0;i<k;i++) {
			for (TypedName key: keySet()) {
				res.add(new SignalName(key,i));
			}
		}
		return res;
	}
	
	public IntervalVector(IntervalVector x) {
		super();
		for (TypedName key: x.keySet()) {
			put(key,x.get(key));
		}
	}
	
	@Override
	public String toString() {
		String res = "(\n";
		for (TypedName key: keySet()) {
			res += "  " + key + ":" + get(key).toString() + "\n";
		}
		return res + ")\n"; 
	}

	@Override
	public IntervalVector copy() {
		return new IntervalVector(this);
	}

	@Override
	public Vector<FuzzMInterval> add(Vector<FuzzMInterval> x) {
		assert(false);
		return null;
	}

	@Override
	public Vector<FuzzMInterval> sub(Vector<FuzzMInterval> x) {
		assert(false);
		return null;
	}

	@Override
	public Vector<FuzzMInterval> mul(BigFraction x) {
		assert(false);
		return null;
	}

}
