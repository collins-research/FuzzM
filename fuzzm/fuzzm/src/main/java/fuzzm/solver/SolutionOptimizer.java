/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.solver;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;

import fuzzm.util.RatSignal;
import fuzzm.util.RatVect;
import fuzzm.util.TypedName;
import fuzzm.util.ValueUtil;
import fuzzm.value.poly.GlobalState;
import jkind.interval.BoolInterval;
import jkind.interval.IntEndpoint;
import jkind.interval.Interval;
import jkind.interval.NumericEndpoint;
import jkind.interval.NumericInterval;
import jkind.interval.RealEndpoint;
import jkind.lustre.EnumType;
import jkind.lustre.NamedType;
import jkind.lustre.SubrangeIntType;
import jkind.lustre.Type;
import jkind.solvers.Model;
import jkind.translation.Specification;
import jkind.util.BigFraction;
import jkind.util.StreamIndex;
/***
 * 
 * The SolutionOptimizer uses generalization techniques to move
 * a given solution "closer" to a target solution.
 *
 */
public class SolutionOptimizer extends jkind.interval.ModelGeneralizer {

	public SolutionOptimizer(Specification spec, String property, Model model, int k) {
		super(spec, property, model, k);
	}
	
	public RatSignal optimize(RatSignal originalSignal, RatSignal targetSignal) {
		RatVect original = originalSignal.encode();
		RatVect target = targetSignal.encode();
		{
			// TODO: Should we perform this loop more than once?  It is possible for us to
			// "avoid obstacles" during optimization.  Every iteration either leaves us the
			// same or closer to the goal.  However, it is also possible to take very small 
			// steps towards a very distant goal.
			//
			if (!modelConsistent()) { // This fills the initial toGeneralize queue as a side-effect
				throw new IllegalStateException("Internal JKind error during optimization");
			}
			while (!toGeneralize.isEmpty()) {
				List<StreamIndex> zed = new ArrayList<StreamIndex>(toGeneralize);
				toGeneralize.clear();
				while (! zed.isEmpty()) {
					StreamIndex si = zed.remove(GlobalState.oracle().nextInt(zed.size()));
					Interval interval = originalInterval(si);
					String key = si.getEncoded().str;
					NamedType ntype = (NamedType) spec.typeMap.get(si.getStream());
					TypedName tname = new TypedName(key,ntype);
					if (target.containsKey(tname)) {
						interval = optimizeInterval(si,target.get(tname));
					} else {
						interval = ValueUtil.BigFractionInterval(original.get(tname),ntype);
					}
					generalized.put(si, interval);
				}
			}
		}
		RatSignal res = new RatSignal(originalSignal);
		for (StreamIndex enc: generalized.keySet()) {
			String key = enc.getStream();
			int time   = enc.getIndex();
			BigFraction value = ValueUtil.BigFractionValue(generalized.get(enc));
			res.put(time,new TypedName(key,(NamedType) spec.typeMap.get(key)),value);
		}
		
		optImproveAssert(res, targetSignal, originalSignal);	
		return res;
	} // end optimize
	
	void optImproveAssert (RatSignal opt, RatSignal target, RatSignal original){			
		if(target.isEmpty())
			assert(opt.equals(original));
		else{
			BigFraction optToTarget = dist(opt, target);
			BigFraction origToTarget = dist(original, target);
			
			int compRes = optToTarget.compareTo(origToTarget);
			assert (compRes <= 0);
		}		
	} 
	
	private static BigFraction dist(RatSignal s1, RatSignal s2){	
		RatSignal diff = s2.sub(s1);
		BigFraction res = diff.dot(diff);		
		return res;
	}
	
	private static NumericEndpoint boundTarget(NumericEndpoint target, NumericInterval interval) {
		if (target.compareTo(interval.getLow()) < 0) {
			return interval.getLow();
		}
		if (interval.getHigh().compareTo(target) < 0) {
			return interval.getHigh();
		}
		return target;
	}
	
	private Interval optimizeInterval(StreamIndex si, BigFraction target) {
		Type type = spec.typeMap.get(si.getStream());
		if (type == NamedType.BOOL) {
			return optimizeBoolInterval(si,! target.equals(BigFraction.ZERO));
		} else if (type == NamedType.INT) {
			NumericInterval initial = (NumericInterval) originalInterval(si);
			NumericEndpoint tgt = new IntEndpoint(target.getNumerator());
			Interval res = optimizeIntInterval(si, initial,tgt);
			return res;
		} else if (type == NamedType.REAL) {
			NumericInterval initial = (NumericInterval) originalInterval(si);
			NumericEndpoint tgt = new RealEndpoint(target);
			return optimizeRealInterval(si, initial,tgt);
		} else if ((type instanceof SubrangeIntType) || (type instanceof EnumType)) {
			return optimizeEnumInterval(si,target.getNumerator());
		} else {
			throw new IllegalArgumentException("Unknown type in generalization: " + type);
		}
	}
	
	private Interval optimizeBoolInterval(StreamIndex si, boolean target) {
		if (modelConsistent(si, BoolInterval.ARBITRARY)) {
			return target ? BoolInterval.TRUE : BoolInterval.FALSE;
		} else {
			return originalInterval(si);
		}
	}

	public Interval optimizeRealInterval(StreamIndex si, NumericInterval initial, NumericEndpoint target) {
		NumericInterval next = new NumericInterval(target,target);
		if (modelConsistent(si, next)) {
			return next;
		}
		next = realIntervalGeneralizer.generalize(si,initial);
		NumericEndpoint opt  = boundTarget(target,next);
		next = new NumericInterval(opt,opt);		
		boolean result = modelConsistent(si, next);
		assert(result);
		return next;
	}
	
	public NumericInterval optimizeIntInterval(StreamIndex si, NumericInterval initial, NumericEndpoint target) {
		NumericInterval next = new NumericInterval(target,target);
		if (modelConsistent(si, next)) {
			return next;
		}
		next = intIntervalGeneralizer.generalize(si,initial);
		NumericEndpoint opt  = boundTarget(target,next);
		next = new NumericInterval(opt,opt);		
		boolean result = modelConsistent(si, next);
		assert(result);
		return next;
	}
	
	private Interval optimizeEnumInterval(StreamIndex si, BigInteger target) {
		NumericInterval next = new NumericInterval(new IntEndpoint(target), new IntEndpoint(target));
		if (modelConsistent(si, next)) {
			return next;
		} else {
			return originalInterval(si);
		}
	}	

}
