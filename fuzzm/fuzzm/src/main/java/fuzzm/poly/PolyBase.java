/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.poly;

import java.math.BigInteger;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.NavigableSet;
import java.util.Set;
import java.util.TreeSet;
import java.util.function.BiFunction;
import java.util.function.Function;

import fuzzm.value.instance.RationalInfinity;
import jkind.util.BigFraction;
import jkind.util.Util;

public class PolyBase extends AbstractPoly {

	Map<VariableID,BigFraction> coefficients;
	BigFraction constant = BigFraction.ZERO;
	
	public PolyBase(){
		this.coefficients = new HashMap<VariableID,BigFraction>();
	}
	
	public PolyBase(VariableID x){
		this.coefficients = new HashMap<VariableID,BigFraction>();
		coefficients.put(x, BigFraction.ONE);
	}
	
	public PolyBase(BigFraction constant){
		this.coefficients = new HashMap<VariableID,BigFraction>();
		this.constant = constant;
	}
	
	public PolyBase(BigFraction coeff, VariableID x){
		this.coefficients = new HashMap<VariableID,BigFraction>();
		this.constant = BigFraction.ZERO;
		this.coefficients.put(x, coeff);
	}
	
	public PolyBase(Map<VariableID,BigFraction> coefficientsIn){
		this.coefficients = normalizeCoefficients(coefficientsIn);
	}
	
	public PolyBase(Map<VariableID,BigFraction> coefficientsIn, BigFraction constant){
		this.coefficients = normalizeCoefficients(coefficientsIn);
		this.constant = constant;
	}
	
	private static Map<VariableID,BigFraction> normalizeCoefficients(Map<VariableID,BigFraction> cIn){
		Map<VariableID,BigFraction> res = new HashMap<VariableID,BigFraction>(cIn);
		cIn.forEach((key,val) -> {
			if(val.compareTo(BigFraction.ZERO) == 0){
				res.remove(key);
			}
		});
		return res;
	}
	
	@Override
	public Iterator<VariableID> iterator() {
		return coefficients.keySet().iterator();
	}

	// solve(x) solves the poly for x by dividing 
	// all other coefficients by the negation of the
	// coefficient of x and removing x;
	@Override
	public PolyBase solveFor(VariableID x) {
		//System.out.println(ID.location() + "solveFor(" + x + "," + this + ")");
		if(!coefficients.containsKey(x)){
			throw new IllegalArgumentException();
		}
		BigFraction xCoef = coefficients.get(x);
		BigFraction xCoefNegated = xCoef.negate();
		Map<VariableID,BigFraction> res = new HashMap<VariableID,BigFraction>(coefficients);
		res.remove(x);
		res.replaceAll((k,v) -> v.divide(xCoefNegated));
		BigFraction newConstant = constant.divide(xCoefNegated);
		return new PolyBase(res,newConstant);
	}

	@Override
	public BigFraction getCoefficient(VariableID x) {
		if(coefficients.containsKey(x)){
			return coefficients.get(x);
		}
		else{
			return BigFraction.ZERO;
		}
	}

	@Override
	public PolyBase negate() {
		Function<BigFraction, BigFraction> neg = (lhs) -> lhs.negate();
		return unaryOpGen(neg);
	}

	@Override
	public PolyBase add(AbstractPoly x) {
		BiFunction<BigFraction, BigFraction, BigFraction> add = (lhs,rhs) -> lhs.add(rhs);
		return binaryOpGen(add,x);
	}
	
	@Override
	public PolyBase add(BigFraction val) {
		Map<VariableID,BigFraction> newCoefs = new HashMap<VariableID,BigFraction>(coefficients);
		BigFraction newConstant = constant.add(val);
		return new PolyBase(newCoefs,newConstant);
	}
	
	@Override
	public PolyBase subtract(AbstractPoly x) {
		BiFunction<BigFraction, BigFraction, BigFraction> sub = (lhs,rhs) -> lhs.subtract(rhs);
		return binaryOpGen(sub,x);
	}
	
	@Override
	public PolyBase subtract(BigFraction val) {
		Map<VariableID,BigFraction> newCoefs = new HashMap<VariableID,BigFraction>(coefficients);
		BigFraction newConstant = constant.subtract(val);
		return new PolyBase(newCoefs,newConstant);
	}

	@Override
	public PolyBase multiply(BigFraction c) {
		Function<BigFraction, BigFraction> mul = (lhs) -> lhs.multiply(c);
		return unaryOpGen(mul);
	}

	@Override
	public PolyBase divide(BigFraction v) {
		Function<BigFraction, BigFraction> div = (lhs) -> lhs.divide(v);
		return unaryOpGen(div);
	}

	private PolyBase unaryOpGen (Function<BigFraction, BigFraction> f) {
		Map<VariableID,BigFraction> res = new HashMap<VariableID,BigFraction>(coefficients);
		res.replaceAll((k,v) -> f.apply(v));	
		BigFraction newConstant = f.apply(constant);
		return new PolyBase(res,newConstant);
	}

	private PolyBase binaryOpGen (BiFunction<BigFraction, BigFraction, BigFraction> f, AbstractPoly x){
		Map<VariableID,BigFraction> res = new HashMap<VariableID,BigFraction>(coefficients);
		Map<VariableID,BigFraction> toAdd = ((PolyBase) x).coefficients;
		toAdd.forEach((var,val) -> { 
			BigFraction myCoefficient = getCoefficient(var);
			res.put(var, f.apply(myCoefficient,val));
		});
		BigFraction newConstant = f.apply(constant, x.getConstant());
		return new PolyBase(res,newConstant);
	}

	@Override
	public boolean isConstant() {
		return coefficients.keySet().isEmpty();
	}

	@Override
	public BigFraction getConstant() {
		return constant;
	}

	@Override
	public VariableID leadingVariable() {
		if(isConstant()) {
			throw new IllegalArgumentException();
		}
		VariableID res = null;
		for(VariableID var : coefficients.keySet()) {
			if ((res == null) || (var.compareTo(res) >= 0)) {
				res = var;
			}
		}
		assert(! (res == null));
		return res;
	}

	@Override
	public VariableID trailingVariable() {
		if(isConstant()) {
			throw new IllegalArgumentException();
		}
		VariableID res = null;
		for(VariableID var : coefficients.keySet()) {
			if ((res == null) || (var.compareTo(res) <= 0)) {
				res = var;
			}
		}
		assert(! (res == null));
		return res;
	}
	
	private static BigFraction abs(BigFraction x){
		boolean negative = x.signum() < 0;
		return negative ? x.negate() : x;
	}
	
	private static String spaceOp(boolean first, BigFraction coeff, String var){
		//
		// s: sign, m: magnitude, v: variable
		// sm     : poly is just the final constant
		// sm*v   : magnitude of leadinv variable coeff != 1
		// s*v    : magnitude of leading variable coeff == 1
		// s_m*v  : subsequent variable with coeff != 1
		// s_v    : subsequent variable with coeff == 1
		// s_m    : final constant
		String res = "";

		// Just the coefficient ..
		boolean validVar = (var != null);
		if (first && !validVar)
			return coeff.toString();

		// Ignore value ..
		boolean zero = (coeff.signum() == 0);
		boolean no_value = ((! first) && zero);
		if (no_value) 
			return res;		

		// Include pre-space ..
		if (! first) {
			res += " ";
		}
		
		// Include sign ..
		boolean explicit_positive = (! first);
		String sign = (coeff.signum() < 0) ? "-" : (explicit_positive ? "+" : "");
		res += sign;

		// Include sign space ..
		String sign_space = (! first) ? " " : "";
		res += sign_space;

		// Include magnitude ..
		BigFraction mag = abs(coeff);
		boolean  one = (mag.compareTo(BigFraction.ONE) == 0);
		boolean include_magnitude = !(validVar && one);
		if (include_magnitude) {
			res += mag.toString();
		}

		// Include multiplication ..
		if (include_magnitude && validVar) {
			res += "*";
		}
		
		// Include variable ..
		if (validVar) {
			res += var;
		}

		return res;
	}
	
	@Override
	public String toString() {
		String res = "";
		res += "(";
		boolean first = true;
		TreeSet<VariableID> keys = new TreeSet<>(coefficients.keySet());
		NavigableSet<VariableID> rkeys = keys.descendingSet();
		for(VariableID var : rkeys) {
			BigFraction val = coefficients.get(var);
			res += spaceOp(first,val,var.toString());
			first = false;
		}	
		res += spaceOp(first,constant,null);		
		res += ")";
		return res;
	}
	
	@Override
	public String cexString() {
		String res = "";
		res += "(";
		boolean first = true;
		for(VariableID var : this) {
			BigFraction val = coefficients.get(var);
			res += spaceOp(first,val,var.cex.toString());
			first = false;
		}	
		res += spaceOp(first,constant,null);		
		res += ")";
		return res;
	}
	
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (! (obj instanceof PolyBase))
			return false;
		PolyBase other = (PolyBase) obj;
		if (!coefficients.equals(other.coefficients) || !constant.equals(other.constant))
			return false;
		return true;
	}

	@Override
	public BigFraction evaluateCEX() {
		BigFraction res = constant;		
		for(VariableID k : coefficients.keySet()) {
			BigFraction v = coefficients.get(k);
			BigFraction cex = k.cex;
			res = res.add(cex.multiply(v));
		}
		return res;
	}

	@Override
	public RegionBounds polyBounds(Map<VariableID, RegionBounds> bounds) {
		RegionBounds res = new RegionBounds(constant);
		for (VariableID v: coefficients.keySet()) {
			if (bounds.containsKey(v)) {
				res = res.accumulate(bounds.get(v).multiply(coefficients.get(v)));
			} else if (coefficients.get(v).signum() != 0) {
				return new RegionBounds(RationalInfinity.NEGATIVE_INFINITY,RationalInfinity.POSITIVE_INFINITY);
			}
		}
		return res;
	}

	@Override
	public BigFraction evaluate(Map<VariableID, BigFraction> bounds) {
		BigFraction res = constant;
		for (VariableID v: coefficients.keySet()) {
			assert(bounds.containsKey(v)) : "Key " + v + " not bound in " + bounds.keySet();
			res = res.add(bounds.get(v).multiply(coefficients.get(v)));
		}
		return res;
	}

	@Override
	public AbstractPoly div(BigInteger d) {
		assert(divisible(d));
		Map<VariableID,BigFraction> Qcoeff = new HashMap<>();
		BigFraction Qconstant = new BigFraction(Util.smtDivide(constant.getNumerator(),d));
		for (VariableID v: coefficients.keySet()) {
			BigInteger c = coefficients.get(v).getNumerator();
			Qcoeff.put(v, new BigFraction(Util.smtDivide(c,d)));
		}
		return new PolyBase(Qcoeff,Qconstant);
	}

	@Override
	public boolean divisible(BigInteger d) {
		if (constant.getDenominator().compareTo(BigInteger.ONE) != 0) return false;
		if (constant.getNumerator().mod(d).signum() != 0) return false;
		for (VariableID v: coefficients.keySet()) {
			BigFraction c = coefficients.get(v);
			if (c.getDenominator().compareTo(BigInteger.ONE) != 0) {
				return false;
			}
			if (c.getNumerator().mod(d).signum() != 0) {
				return false;
			}
		}
		return true;
	}

	public static PolyBase qpoly(BigInteger Q, VariableID k, VariableID m) {
		PolyBase Qk = new PolyBase(k).multiply(new BigFraction(Q));
		PolyBase mp = new PolyBase(m);
		return Qk.add(mp);
	}

	@Override
	public AbstractPoly rewrite(Map<VariableID, AbstractPoly> rw) {
		AbstractPoly res = new PolyBase(constant);
		for (VariableID v: coefficients.keySet()) {
			BigFraction c = coefficients.get(v);
			AbstractPoly p = rw.get(v);
			if (p == null) {
				res = res.add(new PolyBase(c,v));
			} else {
				res = res.add(p.multiply(c));
			}
		}
		return res;
	}

	@Override
	public String toACL2() {
		String res = "(+ ";
		for(VariableID var : this) {
			res += "(* " + coefficients.get(var) + " (id ," + var + " " + var.cex + "))";
		}
		res += constant.toString();
		res += ")";
		return res;
	}

	@Override
	public Set<VariableID> updateVariableSet(Set<VariableID> in) {
		in.addAll(coefficients.keySet());
		return in;
	}
	
	@Override
	public BigInteger leastCommonDenominator() {
		BigInteger q = constant.getDenominator();
		for (VariableID v: this) {
			BigInteger d = coefficients.get(v).getDenominator();
			BigInteger p = q.multiply(d);
			BigInteger g = q.gcd(d);
			q = p.divide(g);
		}
		return q;
	}

	@Override
	public BigInteger constantLCDContribution() {
		BigInteger q = BigInteger.ONE;
		for (VariableID v: this) {
			BigInteger d = coefficients.get(v).getDenominator();
			BigInteger p = q.multiply(d);
			BigInteger g = q.gcd(d);
			q = p.divide(g);
		}
		BigInteger g = constant.getDenominator().gcd(q);
		return constant.getDenominator().divide(g);
	}

	@Override
	public AbstractPoly remove(VariableID x) {
		Map<VariableID,BigFraction> coefficients = new HashMap<>();
		BigFraction constant = this.constant;
		for (VariableID v:this) {
			if (! v.equals(x)) {
				coefficients.put(v, this.coefficients.get(v));
			}
		}
		return new PolyBase(coefficients,constant);
	}
	
	@Override
	public BigFraction dot(AbstractPoly arg) {
		BigFraction res = BigFraction.ZERO;
		for (VariableID v: this) {
			BigFraction prod = this.coefficients.get(v).multiply(arg.getCoefficient(v));
			res = res.add(prod);
		}
		return res;
	}
	
	@Override
	public int compareTo(AbstractPoly arg) {
		// By convention, smaller variables are considered more significant.
		if (this.isConstant() && arg.isConstant()) {
			return this.getConstant().compareTo(arg.getConstant());
		}
		Collection<VariableID> keys = ((PolyBase) arg).coefficients.keySet();
		keys.addAll(this.coefficients.keySet());
		while (! keys.isEmpty()) {
			VariableID minv = Collections.min(keys);
			BigFraction v = this.getCoefficient(minv);
			BigFraction w = arg.getCoefficient(minv);
			int cmp = v.compareTo(w);
			if (cmp != 0) return cmp;
			keys.remove(minv);
		}
		return 0;
	}

	@Override
	public AbstractPoly remove(AbstractPoly x) {
		Collection<VariableID> keys = ((PolyBase) x).coefficients.keySet();
		Map<VariableID,BigFraction> coefficients = new HashMap<>();
		BigFraction constant = this.constant;
		for (VariableID v:this) {
			if (! keys.contains(v)) {
				coefficients.put(v, this.coefficients.get(v));
			}
		}
		return new PolyBase(coefficients,constant);
	}
	
}
