/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.util;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import jkind.interval.BoolInterval;
import jkind.interval.IntEndpoint;
import jkind.interval.NumericEndpoint;
import jkind.interval.NumericInterval;
import jkind.interval.RealEndpoint;
import jkind.lustre.NamedType;
import jkind.lustre.Node;
import jkind.lustre.Type;
import jkind.lustre.VarDecl;
import jkind.lustre.values.BooleanValue;
import jkind.lustre.values.IntegerValue;
import jkind.lustre.values.RealValue;
import jkind.lustre.values.Value;
import jkind.solvers.Model;
import jkind.solvers.SimpleModel;
import jkind.util.BigFraction;
import jkind.util.StreamIndex;

public class FuzzMModel extends Model {
	
	private final Map<String, Value> values = new HashMap<>();
	List<VarDecl> inputs;
	private int k;

	public FuzzMModel(int k, Node main) {
		super(getVarTypes(main));
		inputs = main.inputs;
		this.k = k;
	}

	public FuzzMModel(Node main, RatSignal init) {
		this(init.size(),main);
		for (int time=0;time<k;time++) {
			RatVect nvec = init.get(time);
			for (TypedName key : nvec.keySet()) {
				BigFraction val = nvec.get(key);
				set(key.name,time,val);
			}
		}
	}
	
	public void fixGeneralization() {
		for (int time=0;time<k;time++) {
			for (int input=0;input<inputs.size();input++) {
				StreamIndex si = new StreamIndex(inputs.get(input).id, time);
				String keyString = si.getEncoded().str;
				if (! values.containsKey(keyString)) {
					// For now, we assume that all numeric value inputs are
					// bound by the model.
					assert(inputs.get(input).type.equals(NamedType.BOOL));
					values.put(keyString,BoolInterval.ARBITRARY);
				}
			}
		}
	}
	
	public SimpleModel toSimpleModel() {
		SimpleModel m = new SimpleModel();
		for (String key: values.keySet()) {
			m.putValue(key,values.get(key));
		}
		for (int time=0;time<k;time++) {
			for (int input=0;input<inputs.size();input++) {
				StreamIndex si = new StreamIndex(inputs.get(input).id, time);
				String keyString = si.getEncoded().str;
				Value z = m.getValue(keyString);
				assert(z != null);
			}
		}
		return m;
	}
	
	private static Map<String,Type> getVarTypes(Node main) {
		List<VarDecl> x = main.inputs;
		Map<String,Type> varTypes = new HashMap<String,Type>();
		for (VarDecl vd : x) {
			varTypes.put(vd.id, vd.type);
		}
		return varTypes;
	}

	private static long count(Value x) {
		if (x instanceof RealValue) {
			return 1L;
		} else if (x instanceof BooleanValue) {
			return 1L;
		} else if (x instanceof IntegerValue) {
			return 1L;
		} else if (x instanceof NumericInterval) {
			NumericInterval val = ((NumericInterval) x);
			NumericEndpoint highEP = val.getHigh();
			NumericEndpoint lowEP  = val.getLow();
			assert(highEP.isFinite());
			assert(lowEP.isFinite());
			long high = (long) highEP.toDouble();
			long  low = (long) lowEP.toDouble();
			long  res = (1 + high - low);
			return res;
		} else if (x instanceof BoolInterval){
			return x.equals(BoolInterval.ARBITRARY) ? 2L : 1L;
		} else {
			assert(false);
		}
		return 0;
	}

	public long size() {	
		long res = 1;
		for (int time=0;time<k;time++) {
			for (int input=0;input<inputs.size();input++) {
				StreamIndex si = new StreamIndex(inputs.get(input).id,time);
				String keyString = si.getEncoded().str;
				Value z = values.get(keyString);
				long cnt = count(z);
				if (cnt > 10000L) {
					return 10000L;
				}
				res *= cnt;
				if (res > 10000L) {
					return 10000L;
				}
			}
		}
		return res;
	}
	
	private BigFraction randomValue(Type type, Value x, BigFraction target) {		
		BigFraction  lowBI =  low(x);
		BigFraction highBI = high(x);
		if (lowBI.equals(highBI)) {
			return lowBI;
		}
		int c1 = target.compareTo(lowBI);
		int c2 = highBI.compareTo(target);
		int bias = (c1 + c2)/2;
		return Rat.biasedRandom(type, true, bias, lowBI, highBI);
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
			assert(lowEP.isFinite());
			if (lowEP instanceof RealEndpoint) {
				return ((RealEndpoint) lowEP).getValue();
			}
			if (lowEP instanceof IntEndpoint) {
				return new BigFraction(((IntEndpoint) lowEP).getValue());
			}
			assert(false);
		} else if (x instanceof BoolInterval) {		
			BoolInterval val = ((BoolInterval) x);
			return (val.isTrue() ? BigFraction.ONE : BigFraction.ZERO);
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
			assert(hiEP.isFinite());
			if (hiEP instanceof RealEndpoint) {
				return ((RealEndpoint) hiEP).getValue();
			}
			if (hiEP instanceof IntEndpoint) {
				return new BigFraction(((IntEndpoint) hiEP).getValue());
			}
			assert(false);
		} else if (x instanceof BoolInterval) {			
			BoolInterval val = ((BoolInterval) x);
			return (val.isFalse() ? BigFraction.ZERO : BigFraction.ONE);
		} else {
			assert(false);
		}
		return BigFraction.ZERO;
	}

	public RatSignal randomInstance(RatSignal target) {
		RatSignal rs = new RatSignal();
		for (int time=0;time<k;time++) {
			RatVect rv = new RatVect();
			RatVect targetv = target.get(time);
			for (VarDecl vd: inputs) {
				StreamIndex si = new StreamIndex(vd.id, time);
				String keyString = si.getEncoded().str;
				Value z = values.get(keyString);
				BigFraction zValue = randomValue(vd.type,z,targetv.get(new TypedName(vd.id,(NamedType) vd.type)));
				rv.put(new TypedName(vd.id,(NamedType) vd.type),zValue);
			}
			rs.add(rv);
		}
		return rs;
	}
	
	@Override
	public Value getValue(String arg0) {
		if (values.containsKey(arg0)) {
			return values.get(arg0);
		}
		System.out.println(ID.location() + "Missing key : " + arg0);
		assert(false);
		return null;
	}

	@Override
	public Set<String> getVariableNames() {
		return values.keySet();
	}
	
	private static Value castValue(String name, BigFraction value, List<VarDecl> decl) {
		for (VarDecl vd: decl) {
			if (vd.id.equals(name)) {
				Type type = vd.type;
				if (type.equals(NamedType.BOOL)) {
					if (value.compareTo(BigFraction.ZERO) != 0) {
						return BooleanValue.TRUE;
					} else {
						return BooleanValue.FALSE;
					}
				} else if (type.equals(NamedType.INT)) {
					return new IntegerValue(value.getNumerator());
				} else if (type.equals(NamedType.REAL)) {
					return new RealValue(value);
				}
			}
		}
		assert(false);
		return null;
	}
	
	public void set(String name, int k, BigFraction value) {
		Value res = castValue(name,value,inputs);
		assert(res != null);
		StreamIndex si = new StreamIndex(name,k);
		String key = si.getEncoded().str; 
		values.put(key,res);
	}

	@Override
	public String toString() {
		String res = "[\n";
		for (int time=0;time<k;time++) {
			res += " time:" + time + " (\n";
			for (int input=0;input<inputs.size();input++) {
				StreamIndex si = new StreamIndex(inputs.get(input).id, time);
				String keyString = si.getEncoded().str;
				if(values.containsKey(keyString)){
					Value z = values.get(keyString);
					res += "  " + inputs.get(input).id + ":[" + z.toString() + "]\n" ;
				}
			}
			res += ")\n";
		}
		res += "]";
		return res;
	}
	
}
