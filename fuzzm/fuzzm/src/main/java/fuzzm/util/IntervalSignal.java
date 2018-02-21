/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.util;

import java.util.List;

import jkind.interval.BoolInterval;
import jkind.interval.IntEndpoint;
import jkind.interval.NumericEndpoint;
import jkind.interval.NumericInterval;
import jkind.interval.RealEndpoint;
import jkind.lustre.NamedType;
import jkind.lustre.VarDecl;
import jkind.lustre.values.BooleanValue;
import jkind.lustre.values.IntegerValue;
import jkind.lustre.values.RealValue;
import jkind.lustre.values.Value;
import jkind.solvers.Model;
import jkind.util.BigFraction;
import jkind.util.StreamIndex;

public class IntervalSignal  extends Signal<IntervalVector> {

	private static final long serialVersionUID = 5365578259283718106L;
	
	public IntervalSignal() {
		super();
	}
	
	public IntervalSignal(int k, List<VarDecl> inputs, Model m, IntervalVector span) {
		for(int time = 0; time < k; time++){
			IntervalVector iv = new IntervalVector();					
			for(VarDecl var : inputs){
				StreamIndex si = new StreamIndex(var.id, time);	
				TypedName tname = new TypedName(var.id, (NamedType) var.type);
				Value v = m.getValue(si);
				if(v == null){
					FuzzMInterval jfi = span.get(tname);
					iv.put(tname, jfi);
				}
				else{
					BigFraction defLow = span.get(tname).min;
					BigFraction defHigh = span.get(tname).max;
					BigFraction offSet = defHigh.subtract(defLow);
					BigFraction lowerBound = low(v, offSet);
					BigFraction upperBound = high(v, offSet);				
					FuzzMInterval jfi = new FuzzMInterval((NamedType) var.type, lowerBound, upperBound);
					iv.put(new TypedName(var.id,(NamedType) var.type), jfi);
				}
			} // end for inputs
			add(iv);
		} // end for time
	}
	
	public IntervalSignal(IntervalSignal x) {
		super();
		for (IntervalVector v: x) {
			add(new IntervalVector(v));
		}
	}
	
	@Override
	public IntervalVector get(int time) {
		if (time < size()) {
			return super.get(time);
		}
		return new IntervalVector();
	}
	
	@Override
	public IntervalVector set(int time, IntervalVector value) {
		if (time < size()) {
			return super.set(time,value);
		}
		for (int i=size();i<time;i++) {
			add(new IntervalVector());
		}
		add(value);
		return value;
	}
	
	public void put(int time, TypedName key, FuzzMInterval value) {
		IntervalVector vect = get(time);
		vect.put(key, value);
		set(time,vect);
	}
	
	public IntervalVector encode() {
		IntervalVector res = new IntervalVector();
		for (int time=0;time<size();time++) {
			IntervalVector vect = get(time);
			for (TypedName key: vect.keySet()) {
				StreamIndex si = new StreamIndex(key.name,time);
				String keyString = si.getEncoded().str;
				res.put(new TypedName(keyString,key.type),vect.get(key));
			}
		}
		return res;
	}	
	
	public RatSignal biasedRandomInstance(RatSignal target) {
		RatSignal rs = new RatSignal();
		for (int time=0;time<size();time++) {
			RatVect rv = new RatVect();
			RatVect targetv = target.get(time);
			IntervalVector iv = get(time);
			for (TypedName name: iv.keySet()) {
				FuzzMInterval jfi = iv.get(name);
				BigFraction zValue = biasedRandomValue(jfi,targetv.get(name));
				rv.put(name,zValue);
			}
			rs.add(rv);
		}
		return rs;
	}
	
	public RatSignal uniformRandomInstance() {
		RatSignal rs = new RatSignal();
		for (int time=0;time<size();time++) {
			RatVect rv = new RatVect();
			IntervalVector iv = get(time);
			for (TypedName name: iv.keySet()) {
				FuzzMInterval jfi = iv.get(name);
				BigFraction zValue = jfi.uniformRandom();
				rv.put(name,zValue);
			}
			rs.add(rv);
		}
		return rs;
	}
	
	private BigFraction biasedRandomValue(FuzzMInterval x, BigFraction target) {
		BigFraction  lowBI =  x.min;
		BigFraction highBI = x.max;
		int c1 = target.compareTo(lowBI);
		int c2 = highBI.compareTo(target);
		int bias = (c1 + c2)/2;
		return Rat.biasedRandom(x.type, true, bias, lowBI, highBI);
	}
	
	public static final long MAX_MODEL_SIZE = 1000L;
	
	@Override
	public String toString() {
		int time = 0;
		String res = "[\n";
		for (IntervalVector v: this) {
			res += " time:" + time++ + " ";
			res += v.toString();
		}
		return res + "]"; 
	}
	public static BigFraction low(Value x, BigFraction offSet) {
		if (x instanceof RealValue) {
			RealValue val = ((RealValue) x);
			return val.value;
		} else if (x instanceof BooleanValue) {
			BooleanValue val = ((BooleanValue) x);
			return (val.value ? BigFraction.ONE : BigFraction.ZERO);
		} else if (x instanceof IntegerValue) {
			IntegerValue val = ((IntegerValue) x);
			return new BigFraction(val.value);
		} else if (x instanceof NumericInterval) {
			NumericInterval val = ((NumericInterval) x);
			NumericEndpoint lowEP  = val.getLow();
			boolean isRealEP = lowEP instanceof RealEndpoint;
			if(!isRealEP)
				assert (lowEP instanceof IntEndpoint);
			
			if(! lowEP.isFinite()){
				if (! val.getHigh().isFinite()){
					NamedType nt = (isRealEP ? NamedType.REAL : NamedType.INT);
					return FuzzMInterval.defaultLow(nt);
				}
				else{
					NumericEndpoint hiEP = val.getHigh();
					BigFraction actual = (isRealEP ? ((RealEndpoint) hiEP).getValue()
												   : new BigFraction(((IntEndpoint) hiEP).getValue())
											);
					return actual.subtract(offSet);
				}				
			}
			else{
				return (isRealEP ? ((RealEndpoint) lowEP).getValue() 
								 : new BigFraction (((IntEndpoint) lowEP).getValue()));
			}
		} else if (x instanceof BoolInterval) {			
			return BigFraction.ZERO;
		} else {
			assert(false);
		}
		return BigFraction.ZERO;
	}

	public static BigFraction high(Value x, BigFraction offSet) {
		if (x instanceof RealValue) {
			RealValue val = ((RealValue) x);
			return val.value;
		} else if (x instanceof BooleanValue) {
			BooleanValue val = ((BooleanValue) x);
			return (val.value ? BigFraction.ONE : BigFraction.ZERO);
		} else if (x instanceof IntegerValue) {
			IntegerValue val = ((IntegerValue) x);
			return new BigFraction(val.value);
		} else if (x instanceof NumericInterval) {
			NumericInterval val = ((NumericInterval) x);
			NumericEndpoint hiEP  = val.getHigh();		
			boolean isRealEP = hiEP instanceof RealEndpoint;
			if(!isRealEP)
				assert (hiEP instanceof IntEndpoint);
			
			if(! hiEP.isFinite()){
				if (! val.getLow().isFinite()){
					NamedType nt = (isRealEP ? NamedType.REAL : NamedType.INT);
					return FuzzMInterval.defaultHigh(nt);
				}
				else{
					NumericEndpoint lowEP = val.getLow();
					BigFraction actual = (isRealEP ? ((RealEndpoint) lowEP).getValue()
												   : new BigFraction(((IntEndpoint) lowEP).getValue())
											);
					return actual.add(offSet);
				}				
			}
			else{
				return (isRealEP ? ((RealEndpoint) hiEP).getValue() 
								 : new BigFraction (((IntEndpoint) hiEP).getValue()));
			}					
		} else if (x instanceof BoolInterval) {			
			return BigFraction.ONE;
		} else {
			assert(false);
		}
		return BigFraction.ZERO;
	}
	
	public static BigFraction low(Value x) {
		if (x instanceof RealValue) {
			RealValue val = ((RealValue) x);
			return val.value;
		} else if (x instanceof BooleanValue) {
			BooleanValue val = ((BooleanValue) x);
			return (val.value ? BigFraction.ONE : BigFraction.ZERO);
		} else if (x instanceof IntegerValue) {
			IntegerValue val = ((IntegerValue) x);
			return new BigFraction(val.value);
		} else if (x instanceof NumericInterval) {
			NumericInterval val = ((NumericInterval) x);
			NumericEndpoint lowEP  = val.getLow();
			//assert(lowEP.isFinite());
			boolean isRealEP = lowEP instanceof RealEndpoint;
			if (!isRealEP)
				assert (lowEP instanceof IntEndpoint);
			
			if(! lowEP.isFinite()){
				NamedType nt = (isRealEP ? NamedType.REAL : NamedType.INT);
				return FuzzMInterval.defaultLow(nt);
			}
			else{
				return (isRealEP ? ((RealEndpoint) lowEP).getValue()
						: new BigFraction(((IntEndpoint) lowEP).getValue()));
			}
		} else if (x instanceof BoolInterval) {			
			return BigFraction.ZERO;
		} else {
			assert(false);
		}
		return BigFraction.ZERO;
	}

	public static BigFraction high(Value x) {
		if (x instanceof RealValue) {
			RealValue val = ((RealValue) x);
			return val.value;
		} else if (x instanceof BooleanValue) {
			BooleanValue val = ((BooleanValue) x);
			return (val.value ? BigFraction.ONE : BigFraction.ZERO);
		} else if (x instanceof IntegerValue) {
			IntegerValue val = ((IntegerValue) x);
			return new BigFraction(val.value);
		} else if (x instanceof NumericInterval) {
			NumericInterval val = ((NumericInterval) x);
			NumericEndpoint hiEP  = val.getHigh();
			//assert(hiEP.isFinite());			
			boolean isRealEP = hiEP instanceof RealEndpoint;
			if (!isRealEP)
				assert (hiEP instanceof IntEndpoint);
			
			if(! hiEP.isFinite()){
				NamedType nt = (isRealEP ? NamedType.REAL : NamedType.INT);
				return FuzzMInterval.defaultHigh(nt);
			}
			else{
				return (isRealEP ? ((RealEndpoint) hiEP).getValue()
						: new BigFraction(((IntEndpoint) hiEP).getValue()));
			}
		} else if (x instanceof BoolInterval) {			
			return BigFraction.ONE;
		} else {
			assert(false);
		}
		return BigFraction.ZERO;
	}
	
}
