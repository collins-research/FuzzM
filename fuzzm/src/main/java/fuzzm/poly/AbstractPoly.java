package jfuzz.poly;

import java.math.BigInteger;
import java.util.Map;
import java.util.Set;

import jkind.util.BigFraction;

abstract public class AbstractPoly implements Iterable<VariableID>, Comparable<AbstractPoly> {
	// solve(x) solves the poly for x by dividing 
	// all other coefficients by the negation of the
	// coefficient of x and removing x;
	public abstract AbstractPoly solveFor(VariableID x);
	public abstract AbstractPoly remove(VariableID x);
	public abstract AbstractPoly remove(AbstractPoly x);
	// The coefficient of variable x, otherwise 0.
	public abstract BigFraction getCoefficient(VariableID x);
	public abstract AbstractPoly negate();
	public abstract AbstractPoly add(AbstractPoly x);
	public abstract AbstractPoly add(BigFraction x);
	public abstract AbstractPoly subtract(AbstractPoly x);
	public abstract AbstractPoly subtract(BigFraction x);
	// contains no variables
	public abstract boolean isConstant();
	// The poly's constant value
	public abstract BigFraction getConstant();
	// Returns the leading variable in this poly.
	// Throws an exception if this is constant.
	public abstract VariableID leadingVariable();
	public abstract VariableID trailingVariable();
	public abstract BigFraction evaluateCEX();
	public abstract AbstractPoly multiply(BigFraction v);
	public abstract AbstractPoly divide(BigFraction v);
	public abstract AbstractPoly div(BigInteger d);
	public abstract boolean divisible(BigInteger d);
	public abstract RegionBounds polyBounds(Map<VariableID,RegionBounds> bounds);
	public abstract BigFraction evaluate(Map<VariableID,BigFraction> bounds);
	public abstract AbstractPoly rewrite(Map<VariableID,AbstractPoly> rw);
	public abstract String toACL2();
	public abstract Set<VariableID> updateVariableSet(Set<VariableID> in);
	public abstract BigInteger leastCommonDenominator();
	public abstract String cexString();
	public abstract BigInteger constantLCDContribution();
	public abstract BigFraction dot(AbstractPoly arg);
}
