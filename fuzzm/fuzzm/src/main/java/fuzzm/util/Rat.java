/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.util;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.Random;

import fuzzm.poly.EmptyIntervalException;
import fuzzm.value.hierarchy.EvaluatableValue;
import fuzzm.value.instance.BooleanValue;
import fuzzm.value.instance.IntegerValue;
import fuzzm.value.instance.RationalValue;
import jkind.lustre.BinaryExpr;
import jkind.lustre.BinaryOp;
import jkind.lustre.CastExpr;
import jkind.lustre.Expr;
import jkind.lustre.IdExpr;
import jkind.lustre.IfThenElseExpr;
import jkind.lustre.NamedType;
import jkind.lustre.RealExpr;
import jkind.lustre.Type;
import jkind.util.BigFraction;

public class Rat {

	public static final Random oracle = new Random();
	
	public static BigFraction BigFractionFromString(String value){
		String[] strs = value.split("/");
		if (strs.length <= 2) {
			BigInteger num = new BigInteger(strs[0]);
			if (strs.length > 1) {
				BigInteger denom = new BigInteger(strs[1]);
				return new BigFraction(num, denom);
			}
			return new BigFraction(num);
		}
		else{
			throw new IllegalArgumentException("Couldn't parse string argument \"" + value + "\" as a BigFraction");
		}
	}
	
	public static NamedType TypeFromString(String type) {
		if (type.equals("int")) return NamedType.INT;
		if (type.equals("bool")) return NamedType.BOOL;
		if (type.equals("real")) return NamedType.REAL;
		throw new IllegalArgumentException("Couldn't interpret string argument \"" + type + "\" as a NamedType");
	}
	
	public static EvaluatableValue ValueFromTypedFraction(NamedType ntype, BigFraction fvalue) {
		if (ntype == NamedType.REAL) return new RationalValue(fvalue);
		if (fvalue.getDenominator().compareTo(BigInteger.ONE) == 0) {
			if (ntype == NamedType.INT)  return new IntegerValue(fvalue.getNumerator());
			if (ntype == NamedType.BOOL) {
				if (fvalue.getNumerator().compareTo(BigInteger.ZERO) == 0) return BooleanValue.FALSE;
				if (fvalue.getNumerator().compareTo(BigInteger.ONE)  == 0) return BooleanValue.TRUE;
			}
		}
		throw new IllegalArgumentException("Value " + fvalue + " should be integral");
	}
	
	public static EvaluatableValue ValueFromString(String type, String value) {
		BigFraction fvalue = BigFractionFromString(value);
		NamedType ntype = TypeFromString(type);
		return ValueFromTypedFraction(ntype,fvalue);
	}
	
	public static Expr toExpr(BigFraction x) {
		Expr N = new RealExpr(new BigDecimal(x.getNumerator()));
		Expr D = new RealExpr(new BigDecimal(x.getDenominator()));
		if (x.getDenominator().equals(BigInteger.ONE)) {
			return N;
		}
		System.out.println(ID.location() + "Rational : " + x);
		Expr res = new BinaryExpr(N,BinaryOp.DIVIDE,D);
		return res;
	}
	
	public static Expr cast(String name, Type type) {
		Expr res = new IdExpr(name);
		if (type == NamedType.BOOL) {
			res = new IfThenElseExpr(res,new RealExpr(BigDecimal.ONE),new RealExpr(BigDecimal.ZERO));
		} else if (type == NamedType.INT) {
			res = new CastExpr(NamedType.REAL,res);
		}
		return res;
	}
	
	// this is purely for testing
	protected static double pubBias (double rnd, int bias){
		return bias(rnd, bias);
	}
	private static double bias(double rnd, int bias) {
		assert(-1 <= bias && bias <= 1);
		// So now we want to bias the selection towards the target
		// in some reasonable way.  We consider three cases and
		// define three cutoff values in the range [0.0 .. 1.0):
		//
		// target to the left of range : 1/3
		// target within the range     : 1/2
		// target to the right of range: 2/3
		//
		// We then use an (x-cutoff)^4 cumulative probability 
		// distribution.  The 4th power is sharper than a
		// simple quadratic but simpler to invert than a 3rd
		// power.
		//
		// The result should be that we prefer values near the
		// extremes of the range and prefer values closer to 
		// the target (when the target is not in range) by a 
		// 2:1 ratio.
		//		
		double cutoff  = 0.5 - bias*(0.5 - 1.0/3.0);
		double sign = 0.0;
		if (rnd < cutoff) {
			rnd = rnd/cutoff;
			sign = -cutoff;
		} else {
			rnd = (rnd - cutoff)/(1.0 - cutoff);
			sign = (1.0 - cutoff);
		}
		rnd = cutoff + sign*Math.sqrt(Math.sqrt(rnd));
		return rnd;
	}
	
	private static BigFraction biasedRandom(boolean biased, int bias, BigFraction min, BigFraction max) {
		double drnd = bias(oracle.nextDouble(),bias);
		BigDecimal rnd = BigDecimal.valueOf(drnd);
		BigFraction r = BigFraction.valueOf(rnd);
		BigFraction offset = (max.subtract(min)).multiply(r);
		BigFraction res = min.add(offset);
		return res;
	}
	
	public static BigFraction biasedRandom(Type type, boolean biased, int bias, BigFraction min, BigFraction max) {
		BigFraction res = null;
		if (type == NamedType.REAL) {
			res = biasedRandom(biased,bias,min,max);
		} else if (type == NamedType.BOOL) {
			if (min.compareTo(max) == 0) return min;
			res = oracle.nextBoolean() ? BigFraction.ONE : BigFraction.ZERO;
		} else {
			// it should be an invariant that the denominator is ONE
			BigFraction imin = roundUp(min);
			BigFraction imax = roundDown(max);
			if (imin.compareTo(imax) >= 0) {
				if (imin.compareTo(imax) == 0) return imin;
				throw new EmptyIntervalException();
			}
			res = biasedRandom(biased,bias,imin,imax.add(BigFraction.ONE));
			res = res.subtract(imin); 
			BigInteger N = res.getNumerator();
			BigInteger D = res.getDenominator();
			BigInteger Q = N.divide(D);
			res = new BigFraction(Q).add(imin);			
		}
		assert(min.compareTo(res) <= 0) && (res.compareTo(max) <= 0);
		return res;
	}
	
	public static BigFraction roundDown(BigFraction max) {
		BigInteger div[] = max.getNumerator().divideAndRemainder(max.getDenominator());
		BigInteger Q = div[0];
		BigInteger R = div[1];
		BigFraction res;
		if (R.signum() == 0) {
			res = new BigFraction(Q);
		} else if (R.signum() < 0) {
			res = new BigFraction(Q.subtract(BigInteger.ONE));
		} else {
			res = new BigFraction(Q);
		}
		assert(res.compareTo(max) <= 0)        : "Rounding down : " + res + " <= " + max + " (" + Q + "*" + max.getDenominator() + " + " + R + ")";
		assert(max.signum()*res.signum() >= 0) : "Rounding down : " + res + " <= " + max + " (" + Q + "*" + max.getDenominator() + " + " + R + ")" ;
		assert(max.subtract(res).compareTo(BigFraction.ONE) <= 0);
		return res;
	}
	
	public static BigFraction roundUp(BigFraction min) {
		BigInteger div[] = min.getNumerator().divideAndRemainder(min.getDenominator());
		BigInteger Q = div[0];
		BigInteger R = div[1];
		BigFraction res;
		if (R.signum() == 0) {
			res = new BigFraction(Q);
		} else if (R.signum() > 0) {
			res = new BigFraction(Q.add(BigInteger.ONE));
		} else {
			res = new BigFraction(Q);
		}
		assert(res.compareTo(min) >= 0)        : "Rounding up : " + res + " >= " + min + " (" + Q + "*" + min.getDenominator() + " + " + R + ")";
		assert(min.signum()*res.signum() >= 0) : "Rounding up : " + res + " >= " + min + " (" + Q + "*" + min.getDenominator() + " + " + R + ")";
		assert(res.subtract(min).compareTo(BigFraction.ONE) <= 0);
		return res;		
	}
	
}
