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

import jkind.interval.BoolInterval;
import jkind.interval.IntEndpoint;
import jkind.interval.Interval;
import jkind.interval.NumericEndpoint;
import jkind.interval.NumericInterval;
import jkind.interval.RealEndpoint;
import jkind.lustre.NamedType;
import jkind.lustre.Type;
import jkind.lustre.values.BooleanValue;
import jkind.lustre.values.IntegerValue;
import jkind.lustre.values.RealValue;
import jkind.lustre.values.Value;
import jkind.util.BigFraction;

/***
 * 
 * ValueUtil contains utility functions that perform various 
 * casts between Value, BigFraction, and Dimension objects.
 *
 */
public class ValueUtil {
	
	/***
	 * 
	 * Cast a Value (and its Type) to a Dimension (of the same Type).
	 * @param v Value to cast. 
	 * @param vType Type of resulting Dimension (should correspond to v).
	 * @return If v is an Interval, its endpoints become min and max of the resulting Dimension.
	 * 	       If v is a primitive value (or BoolInterval), return a "degenerate" Dimension (min=max).
	 * 	       For boolean values/intervals, falseness represented as ZERO, trueness as ONE.
	 */
	public static FuzzMInterval valueToDim (Value v, NamedType vType){
		BigFraction lowDim, highDim;
		lowDim = highDim = BigFraction.ZERO;
		
		boolean intVal = v instanceof IntegerValue;
		boolean realVal = v instanceof RealValue;
		if(intVal){
			v = (IntegerValue) v;
			BigInteger a = ((IntegerValue) v).value;
			IntEndpoint ie = new IntEndpoint(a);
			v = new NumericInterval (ie,ie);
		}
		else if (realVal){
			v = (RealValue) v;
			BigFraction a = ((RealValue) v).value;
			RealEndpoint re = new RealEndpoint(a);
			v = new NumericInterval (re,re);
		}
		
		if(v instanceof NumericInterval){
			NumericInterval ni = (NumericInterval) v;
			boolean intInterval = ni.getLow() instanceof IntEndpoint;
			boolean realInterval = ni.getLow() instanceof RealEndpoint;
			
			if(intInterval){	
				IntEndpoint iel = (IntEndpoint) ni.getLow();
				lowDim = new BigFraction (iel.getValue());
				IntEndpoint ieh = (IntEndpoint) ni.getHigh();
				highDim = new BigFraction(ieh.getValue());
			}
			if(realInterval){
				lowDim = ((RealEndpoint) (ni.getLow())).getValue();
				highDim = ((RealEndpoint) (ni.getLow())).getValue();
			}
		}
		
		if(v instanceof BooleanValue){
			v = (BooleanValue) v;
			boolean val = ((BooleanValue) v).value;
			lowDim = highDim = (val ? BigFraction.ONE : BigFraction.ZERO);
		}
		
		if(v instanceof BoolInterval){
			v = (BoolInterval) v;
			boolean val = ((BoolInterval) v).isTrue();
			lowDim = highDim = (val ? BigFraction.ONE : BigFraction.ZERO);
		}
		
		return new FuzzMInterval(vType, lowDim, highDim);
	} // end valueToDim
	
	/***
	 * 
	 *  Cast a Value to a BigFraction.  If value is an Interval, it will probably be "degenerate" (identical endpoints).
	 *  @param value Value to be casted
	 *  @return If value is an Interval, return the first finite endpoint value.
	 * True boolean values (and intervals) return ONE, otherwise ZERO.
	 * Integer and Real values simply return their value.
	 * Otherwise, return ZERO.
	 */
	public static BigFraction BigFractionValue(Value value) {
		if (value instanceof NumericInterval) {
			NumericEndpoint z = ((NumericInterval) value).getLow();
			if (! z.isFinite()) {
				z = ((NumericInterval) value).getHigh();
				if (! z.isFinite()) {
					return BigFraction.ZERO;
				}
			}			
			if (z instanceof IntEndpoint) {
				return new BigFraction(((IntEndpoint) z).getValue());
			} 
			if (z instanceof RealEndpoint) {
				return ((RealEndpoint) z).getValue();
			}
		}
		if (value instanceof BoolInterval) {
			return value.equals(BoolInterval.TRUE) ? BigFraction.ONE : BigFraction.ZERO;
		}
		if (value instanceof IntegerValue){
			IntegerValue z = (IntegerValue) value;
			BigInteger a = ((IntegerValue) z).value;
			return new BigFraction(a);
		}
		if (value instanceof RealValue){
			RealValue z = (RealValue) value;
			BigFraction a = ((RealValue) z).value;
			return a;
		}
		if (value instanceof BooleanValue){
			BooleanValue z = (BooleanValue) value;
			boolean b = z.value;
			return (b ? BigFraction.ONE : BigFraction.ZERO);
		}
		return BigFraction.ZERO;
	} // end BigFractionValue
	
	/***
	 * 
	 * @param originalVal populates both NumericEndpoints (if type is INT/REAL).  If type is BOOL, originalVal should be ZERO or ONE. 
	 * @param type Interval type (and NumericEndpoint type in numeric cases).
	 * @return When type is numeric, return a "degenerate" Interval (with identical endpoints) 
	 * based on originalVal.  When type is BOOL, return an appropriate BoolInterval.
	 */
	public static Interval BigFractionInterval(BigFraction originalVal, Type type){
		Interval interval;

		if (type == NamedType.INT){
			NumericEndpoint x = new IntEndpoint(originalVal.getNumerator());
			interval = new NumericInterval(x,x);
		}
		else if (type == NamedType.REAL){
			NumericEndpoint x = new RealEndpoint(originalVal);
			interval = new NumericInterval(x,x);
		}
		else if (type == NamedType.BOOL){
			interval = (originalVal.equals(BigFraction.ZERO)) ? BoolInterval.FALSE : BoolInterval.TRUE;
		}
		else{
			throw new IllegalArgumentException("Unsupported input type: "
					+ type.getClass().getName());
		}
		return interval;
	}

}
