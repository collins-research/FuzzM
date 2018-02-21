/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.util;

import java.math.BigInteger;

import fuzzm.poly.EmptyIntervalException;
import jkind.lustre.NamedType;
import jkind.lustre.Type;
import jkind.util.BigFraction;

public class FuzzMInterval {

	public BigFraction min;
	public BigFraction max;
	public NamedType type;
	
	public FuzzMInterval(NamedType type, BigFraction min, BigFraction max) {
		if (! (min.compareTo(max) <= 0)) throw new EmptyIntervalException("Empty FuzzM Interval: [" + min + "," + max + "]");
		if ((type == NamedType.BOOL) && (min.compareTo(max) != 0)) {
		    // TODO: Look for a better solution here ..
			this.min = BigFraction.ZERO;
			this.max = BigFraction.ONE;
		} else {
			this.min = min;
			this.max = max;
		}
		this.type = type;
	}

	public FuzzMInterval(NamedType type, int min, int max){
		this(type, 
				new BigFraction (BigInteger.valueOf(min)),
				new BigFraction (BigInteger.valueOf(max)));
	}

	public FuzzMInterval(NamedType type) {
		this.type = type;
		this.min = defaultLow(type);
		this.max = defaultHigh(type);
	}
	
	public void setMin(BigFraction min) {
		this.min = min;
	}
	
	public void setMax(BigFraction max) {
		this.max = max;
	}
	
	public BigFraction uniformRandom() {
		return Rat.biasedRandom(type,false,0,min,max);
	}
	
	public double getMinVal (){
		return min.doubleValue();
	}
	
	public double getMaxVal (){
		return max.doubleValue();
	}
	
	public BigFraction getRange(){
		return max.subtract(min);
	}
		
	public static FuzzMInterval defaultInterval(NamedType vType){
		FuzzMInterval res = null;	
		BigFraction lowVal = defaultLow(vType);
		BigFraction highVal = defaultHigh(vType);
		res = new FuzzMInterval(vType, lowVal, highVal);	
		return res;
	}
	
	public static BigFraction defaultLow (Type vType){
		if(vType == NamedType.INT || vType == NamedType.REAL) {
			return numericLow();
		}
		else if (vType == NamedType.BOOL) {
			return BigFraction.ZERO;
		}
		else{
			throw new IllegalArgumentException("Unsupported type: "
					+ vType.getClass().getName());
		}
	}
	
	public static BigFraction defaultHigh (Type vType){
		if(vType == NamedType.INT || vType == NamedType.REAL) {
			return numericHigh();
		}
		else if (vType == NamedType.BOOL) {
			return BigFraction.ONE;
		}
		else{
			throw new IllegalArgumentException("Unsupported type: "
					+ vType.getClass().getName());
		}
	}
	
	private static BigFraction numericLow(){
		double range = getNumericRange();	
		double low = -1 * (range / 2);
		return new BigFraction(BigInteger.valueOf((long)low));
	}
	
	private static BigFraction numericHigh(){
		double range = getNumericRange();		
		double high = (range / 2) - 1;
		return new BigFraction(BigInteger.valueOf((long)high));		
	}
	
	private static double getNumericRange(){
		double power = 8;
		double range = Math.pow(2,power);
		return range;
	}
	
	@Override
	public String toString() {
		return "{min: " + this.min + ", max: " + this.max + ", type: " + this.type + "}";
	}
	
}
