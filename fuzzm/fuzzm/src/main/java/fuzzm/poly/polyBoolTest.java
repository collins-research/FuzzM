/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.poly;

import java.math.BigDecimal;

import fuzzm.util.Debug;
import jkind.lustre.NamedType;
import jkind.util.BigFraction;

public class polyBoolTest {

	static BigFraction valueOf(int value) {
		return BigFraction.valueOf(BigDecimal.valueOf(value));
	}
	
	static PolyBase polyConst(int value) {
		return new PolyBase(valueOf(value));
	}
	
	static PolyBase poly4(int cw, VariableID w, int cx, VariableID x, int cy, VariableID y, int cz, VariableID z, int c0) {
		PolyBase pw = new PolyBase(w).multiply(valueOf(cw));
		PolyBase px = new PolyBase(x).multiply(valueOf(cx));
		PolyBase py = new PolyBase(y).multiply(valueOf(cy));
		PolyBase pz = new PolyBase(z).multiply(valueOf(cz));
		PolyBase c  = new PolyBase(valueOf(c0));
		return pw.add(px).add(py).add(pz).add(c);
	}
	
	static PolyBase poly3(int cx, VariableID x, int cy, VariableID y, int cz, VariableID z, int c0) {
		PolyBase px = new PolyBase(x).multiply(valueOf(cx));
		PolyBase py = new PolyBase(y).multiply(valueOf(cy));
		PolyBase pz = new PolyBase(z).multiply(valueOf(cz));
		PolyBase c  = new PolyBase(valueOf(c0));
		return px.add(py).add(pz).add(c);
	}
	
	static PolyBase poly2(int cx, VariableID x, int cy, VariableID y, int c0) {
		PolyBase px = new PolyBase(x).multiply(valueOf(cx));
		PolyBase py = new PolyBase(y).multiply(valueOf(cy));
		PolyBase c  = new PolyBase(valueOf(c0));
		return px.add(py).add(c);
	}
	
	static PolyBase poly1(int cx, VariableID x, int c0) {
		PolyBase px = new PolyBase(x).multiply(valueOf(cx));
		PolyBase c  = new PolyBase(valueOf(c0));
		return px.add(c);
	}
	
	static PolyBool bound(VariableID x, PolyBase lo, PolyBase hi) {
		PolyBool xlo = PolyBool.less0(lo.subtract(new PolyBase(x)));
		PolyBool xhi = PolyBool.greater0(hi.subtract(new PolyBase(x)));
		return xlo.and(xhi);		
	}
	
//	public static void error_6_26_16() {
//		PolyEvaluatableValue min0 = new IntegerPoly(new VariableID("min[0]"));
//		PolyEvaluatableValue in0  = new IntegerPoly(new VariableID("in[0]"));
//		PolyEvaluatableValue in1  = new IntegerPoly(new VariableID("in[1]"));
//		PolyEvaluatableValue in2  = new IntegerPoly(new VariableID("in[2]"));
//		PolyEvaluatableValue min2 = new IntegerPoly(new VariableID("min[2]"));
//		PolyEvaluatableValue min1 = new IntegerPoly(new VariableID("min[1]"));
//		PolyEvaluatableValue v128 = new IntegerPoly(new PolyBase(new BigFraction(BigInteger.valueOf(128))));
//
//		EvaluatableValue c1 = v128.negate().lessequal(min0).and(min0.lessequal(v128.negate()));
//		EvaluatableValue c2 = min0.         lessequal(in0 ).and( in0.less(v128));
//		EvaluatableValue c3 = in0.          lessequal(in1 ).and( in1.less(v128));
//		EvaluatableValue c4 = v128.negate().lessequal( in2).and( in2.less(v128));
//		EvaluatableValue c5 =                         min2.equalop(min0);
//		EvaluatableValue c6 =                         min1.equalop(min2);
//
//		EvaluatableValue r1 = c1.and(c2.and(c3.and(c4.and(c5.and(c6)))));
//		
//	}
	
	public static void main(String[] args) {
		Debug.setEnabled(true);
		VariableID w = VariableID.postAlloc("w",NamedType.REAL,BigFraction.ZERO);
		VariableID x = VariableID.postAlloc("xx",NamedType.REAL,BigFraction.ZERO);
		VariableID y = VariableID.postAlloc("y",NamedType.REAL,BigFraction.ZERO);
		VariableID z = VariableID.postAlloc("z",NamedType.REAL,BigFraction.ZERO);
		// Making sure that restriction does the right thing ..
		PolyBool f1 = PolyBool.greater0(poly2(3,x,-1,y,2));
		PolyBool f2 = PolyBool.greater0(poly2(-5,x,-1,y,10));
		PolyBool f3 = f1.and(f2);
		System.out.println("\nf3 : " + f3.toString());
		// Restriction example from paper ..
		x.setCex(valueOf(4));
		y.setCex(valueOf(1));
		PolyBool e1 = PolyBool.greater0(poly2(1,x,-1,y,2));
		PolyBool e2 = PolyBool.greater0(poly2(-1,x,-1,y,6));
		PolyBool e3 = e1.and(e2);
		System.out.println("\ne3 : " + e3.toString());
		// AND with restriction .. (quadratic) this looks good.
		x.setCex(valueOf(0));
		y.setCex(valueOf(0));
		z.setCex(valueOf(0));
		PolyBool x1 = PolyBool.greater0(poly1(1,x,7)).and(PolyBool.greater0(poly1(-1,x,100)));
		PolyBool x2 = PolyBool.equal0(poly2(3,x,-1,y,7)).not();
		PolyBool x3 = PolyBool.greater0(poly3(2,x,3,y,-1,z,5));
		PolyBool x123 = x1.and(x2).and(x3);
		System.out.println("\nx123 : " + x123);
		PolyBool x4a = PolyBool.greater0(poly1(1,x,15));
		PolyBool x4b = PolyBool.greater0(poly1(-1,x,90));
		System.out.println("x4a : " + x4a);
		System.out.println("x4b : " + x4b);
		PolyBool x4 = x4a.or(x4b);
		System.out.println("or : " + x4);
		PolyBool x5 = PolyBool.greater0(poly2(4,x,-1,y,9)).and(PolyBool.greater0(poly2(-1,x,1,y,7)));
		PolyBool x6 = PolyBool.greater0(poly3(-3,x,5,y,-1,z,1));
		PolyBool x456 = x4.and(x5).and(x6);
		System.out.println("\nx456 : " + x456);
		PolyBool x123456 = x123.and(x456);
		System.out.println("\nx123456 : " + x123456);
		// A more belabored version of our slide example .. 
		x.setCex(valueOf(110));
		y.setCex(valueOf(50));
		z.setCex(valueOf(-50));
		PolyBool xlo = PolyBool.less0(poly2(-1,x,0,y,100));
		PolyBool xhi = PolyBool.greater0(poly2(-1,x,0,y,200));
		PolyBool ylo = PolyBool.less0(poly2(3,x,-1,y,-290));
		PolyBool yhi = PolyBool.greater0(poly2(-3,x,-1,y,970));
		PolyBool zlo = PolyBool.less0(poly4(1,x,1,y,-1,z,0,z,-250));
		PolyBool zhi = PolyBool.greater0(poly4(0,x,-1,y,-1,z,0,w,7));
		PolyBool xbound = xlo.and(xhi);
		PolyBool ybound = xbound.and(ylo).and(yhi);
		PolyBool zbound = ybound.and(zlo).and(zhi);
		System.out.println("\nzbound : " + zbound.toString());
		// This is our polyBool example from our slide deck ..
		xbound = bound(x,polyConst(100),polyConst(200));
		ybound = bound(y,poly1(3,x,-290),poly1(-3,x,970));
		zbound = bound(z,poly2(1,x,1,y,-250),poly1(-1,y,7));
		PolyBool tz = xbound.and(ybound.and(zbound));
		// The normalized expression cannot be 
		System.out.println("\nNormalize : " + tz.toString());
		tz = tz.normalize();
		System.out.println("\nResult : " + tz.toString());
	}
	
}
