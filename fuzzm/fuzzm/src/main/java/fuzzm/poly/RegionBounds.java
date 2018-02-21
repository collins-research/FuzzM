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

import fuzzm.util.Debug;
import fuzzm.util.ID;
import fuzzm.util.FuzzMInterval;
import fuzzm.util.Rat;
import fuzzm.value.hierarchy.RationalType;
import fuzzm.value.instance.BooleanValue;
import fuzzm.value.instance.RationalInfinity;
import fuzzm.value.instance.RationalValue;
import jkind.lustre.NamedType;
import jkind.util.BigFraction;

public class RegionBounds {

	public final RationalType lower;
	public final RelationType lowerType;
	
	public final RelationType rangeType;

	public final RationalType upper;
	public final RelationType upperType;

	public RegionBounds(RationalType lower, RelationType lowerType, RelationType rangeType, RationalType upper, RelationType upperType) {
		this.lower = lower;
		this.lowerType = lowerType;
		this.upper = upper;
		this.upperType = upperType;
		this.rangeType = rangeType;
		if (rangeType == RelationType.INCLUSIVE) {
			BooleanValue res = (BooleanValue) this.lower.lessequal(this.upper);
			if (! res.isTrue()) {
				throw new EmptyIntervalException("Empty Interval [" + lower + "," + upper + "]");
			}
		}
	}
	
	public RegionBounds(RationalType lower, RelationType lowerType, RationalType upper, RelationType upperType) {
		this(lower,lowerType,RelationType.INCLUSIVE,upper,upperType);
	}	

	public RegionBounds(RegionBounds lower, RelationType rangeType, RegionBounds upper) {
		boolean inclusive = rangeType == RelationType.INCLUSIVE;
		this.lower     = inclusive ? lower.lower     : lower.upper;
		this.lowerType = inclusive ? lower.lowerType : lower.upperType;
		this.upper     = inclusive ? upper.upper     : upper.lower;
		this.upperType = inclusive ? upper.upperType : upper.lowerType;
		this.rangeType = rangeType;
		if (inclusive) {
			BooleanValue res = (BooleanValue) this.lower.lessequal(this.upper);
			if (! res.isTrue()) {
				throw new EmptyIntervalException("Empty Interval " + left(this.lowerType) + lower + "," + upper + right(this.upperType));
			}
		}
	}
	
	public RegionBounds(RationalType lower, RationalType upper) {
		this(lower, RelationType.INCLUSIVE, RelationType.INCLUSIVE, upper, RelationType.INCLUSIVE);
	}
	
	public RegionBounds(RationalType value) {
		this(value,value);
	}

	public RegionBounds(BigFraction constant) {
		this(new RationalValue(constant));
	}
	
	private BigFraction maxInterval(NamedType type, BigFraction oldMax) {
		BigFraction res = oldMax;
		if (upper.isFinite()) {
			res = upper.getValue();
			if (type == NamedType.INT && upperType == RelationType.EXCLUSIVE) {
				res = res.subtract(BigFraction.ONE);
			}
		}
		return res;
	}

	private BigFraction minInterval(NamedType type, BigFraction oldMin) {
		BigFraction res = oldMin;
		if (lower.isFinite()) {
			res = lower.getValue();
			if (type == NamedType.INT && lowerType == RelationType.EXCLUSIVE) {
				res = res.add(BigFraction.ONE);
			}
		}
		return res;
	}
	
	public FuzzMInterval updateInterval(FuzzMInterval oldInterval) {
		return new FuzzMInterval(oldInterval.type,minInterval(oldInterval.type,oldInterval.min),maxInterval(oldInterval.type,oldInterval.max));
	}
	
	private static final RationalType ZERO = new RationalValue(BigFraction.ZERO);
	private static final RationalType ONE  = new RationalValue(BigFraction.ONE);
	public static final RegionBounds EMPTY = new RegionBounds(RationalInfinity.NEGATIVE_INFINITY,
														RelationType.EXCLUSIVE,
														RelationType.EXCLUSIVE,
														RationalInfinity.POSITIVE_INFINITY,
														RelationType.EXCLUSIVE);
	
	RegionBounds multiply(BigFraction coefficient) {
		RationalValue value = new RationalValue(coefficient);
		int sign = coefficient.signum();
		if (sign == 0) {
			return new RegionBounds(ZERO,RelationType.INCLUSIVE,ZERO,RelationType.INCLUSIVE);
		}
		if (sign < 0) {
			return new RegionBounds(upper.multiply(value),upperType,lower.multiply(value),lowerType);
		}
		return new RegionBounds(lower.multiply(value),lowerType,upper.multiply(value),upperType);
	}
	
	RegionBounds accumulate(RegionBounds res) {
		return new RegionBounds(lower.plus(res.lower),lowerType.inclusiveAND(res.lowerType),upper.plus(res.upper),upperType.inclusiveAND(res.upperType));
	}

	public RegionBounds intersect(RegionBounds arg) {
		RationalType lower = this.lower.max(arg.lower);
		RationalType upper = this.upper.min(arg.upper);
		return new RegionBounds(lower,upper);
	}

	public RegionBounds union(RegionBounds arg) {
		RationalType lower = this.lower.min(arg.lower);
		RationalType upper = this.upper.max(arg.upper);
		return new RegionBounds(lower,upper);
	}

	private boolean fixed(NamedType type) {
		return (type == NamedType.INT) ?
			(upperType == RelationType.INCLUSIVE) &&
			(lowerType == RelationType.INCLUSIVE) &&
			(!upper.isFinite() || (upper.getValue().getDenominator().compareTo(BigInteger.ONE) == 0)) &&
			(!lower.isFinite() || (lower.getValue().getDenominator().compareTo(BigInteger.ONE) == 0))
			: true;
	}
	
	public BigFraction optimize(NamedType type, BigFraction target) {
		assert(fixed(type));
		RationalValue tgt = new RationalValue(target);
		assert(rangeType == RelationType.INCLUSIVE);
		if (upper.less(tgt).isTrue()) return upper.getValue();
		if (lower.greater(tgt).isTrue()) return lower.getValue();
		return target;
	}

	static String left(RelationType rel) {
		return (rel == RelationType.INCLUSIVE) ? "[" : "(";
	}
	
	static String right(RelationType rel) {
		return (rel == RelationType.INCLUSIVE) ? "]" : ")";
	}
	
	public RegionBounds fix(NamedType type) {
		RationalType lower;
		RationalType upper;
		if (type == NamedType.INT) {
			BigFraction value;
			if (rangeType == RelationType.INCLUSIVE) {
				if (this.lower.isFinite()) {
					value = this.lower.getValue();
					if (value.getDenominator().compareTo(BigInteger.ONE) == 0) {
						if (this.lowerType == RelationType.INCLUSIVE) {
							lower = this.lower;
						} else {
							lower = this.lower.plus(ONE);
						}
					} else {
						lower = new RationalValue(Rat.roundUp(value));
					}
				} else {
					lower = this.lower;
				}
				if (this.upper.isFinite()) {
					value = this.upper.getValue();
					if (value.getDenominator().compareTo(BigInteger.ONE) == 0) {
						if (this.upperType == RelationType.INCLUSIVE) {
							upper = this.upper;
						} else {
							upper = (RationalType) this.upper.minus(ONE);
						}
					} else {
						upper = new RationalValue(Rat.roundDown(value));
					}
				} else {
					upper = this.upper;
				}
				if (Debug.isEnabled()) System.out.println(ID.location() + "Fixing Interval "+ left(this.lowerType) + this.lower + "," + this.upper + right(this.upperType));
				return new RegionBounds(lower,upper);
			} else {
				if (this.lower.isFinite()) {
					value = this.lower.getValue();
					if (value.getDenominator().compareTo(BigInteger.ONE) == 0) {
						if (this.lowerType == RelationType.INCLUSIVE) {
							lower = this.lower;
						} else {
							lower = (RationalType) this.lower.minus(ONE);
						}
					} else {
						lower = new RationalValue(Rat.roundDown(value));
					}
				} else {
					lower = this.lower;
				}
				if (this.upper.isFinite()) {
					value = this.upper.getValue();
					if (value.getDenominator().compareTo(BigInteger.ONE) == 0) {
						if (this.upperType == RelationType.INCLUSIVE) {
							upper = this.upper;
						} else {
							upper = (RationalType) this.upper.plus(ONE);
						}
					} else {
						upper = new RationalValue(Rat.roundUp(value));
					}
				} else {
					upper = this.upper;
				}
				return new RegionBounds(lower,RelationType.INCLUSIVE,RelationType.EXCLUSIVE,upper,RelationType.INCLUSIVE);
			}
		}
		return this;
	}

	public FuzzMInterval fuzzInterval(NamedType type, BigFraction smin, BigFraction smax) {
		BigFraction range = smax.subtract(smin);
		if (upper.isFinite()) {
			if (lower.isFinite()) {
				BigFraction min = lower.getValue();
				BigFraction max = upper.getValue();
				return new FuzzMInterval(type,min,max);
			} else {
				return new FuzzMInterval(type,upper.getValue().subtract(range),upper.getValue());
			}
		} else {
			if (lower.isFinite()) {
				return new FuzzMInterval(type,lower.getValue(),lower.getValue().add(range));
			} else {
				return new FuzzMInterval(type,smin,smax);
			}
		}
	}

	public FuzzMInterval fuzzInterval(FuzzMInterval interval) {
		if (upper.isFinite()) {
			if (lower.isFinite()) {
				BigFraction min = lower.getValue();
				BigFraction max = upper.getValue();
				return new FuzzMInterval(interval.type,min,max);
			} else {
				return new FuzzMInterval(interval.type,interval.min,upper.getValue());
			}
		} else {
			if (lower.isFinite()) {
				return new FuzzMInterval(interval.type,lower.getValue(),interval.max);
			} else {
				return interval;
			}
		}
	}
	
}
