package jfuzz.poly;

import java.math.BigInteger;

import jfuzz.util.Debug;
import jfuzz.util.ID;
import jfuzz.util.JFuzzInterval;
import jfuzz.util.Rat;
import jfuzz.value.hierarchy.RationalType;
import jfuzz.value.instance.BooleanValue;
import jfuzz.value.instance.RationalInfinity;
import jfuzz.value.instance.RationalValue;
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
	
	public JFuzzInterval updateInterval(JFuzzInterval oldInterval) {
		return new JFuzzInterval(oldInterval.type,minInterval(oldInterval.type,oldInterval.min),maxInterval(oldInterval.type,oldInterval.max));
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

	public BigFraction random() {
		// TODO: I think this is where our random functionality should live.
		// This function is a real hack ..
		if (this.lower.isFinite()) return this.lower.getValue();
		if (this.upper.isFinite()) return this.upper.getValue();
		return BigFraction.ZERO;
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

	public JFuzzInterval fuzzInterval(NamedType type, BigFraction smin, BigFraction smax) {
		BigFraction range = smax.subtract(smin);
		if (upper.isFinite()) {
			if (lower.isFinite()) {
				BigFraction min = lower.getValue();
				BigFraction max = upper.getValue();
				return new JFuzzInterval(type,min,max);
			} else {
				return new JFuzzInterval(type,upper.getValue().subtract(range),upper.getValue());
			}
		} else {
			if (lower.isFinite()) {
				return new JFuzzInterval(type,lower.getValue(),lower.getValue().add(range));
			} else {
				return new JFuzzInterval(type,smin,smax);
			}
		}
	}

	public JFuzzInterval fuzzInterval(JFuzzInterval interval) {
		if (upper.isFinite()) {
			if (lower.isFinite()) {
				BigFraction min = lower.getValue();
				BigFraction max = upper.getValue();
				return new JFuzzInterval(interval.type,min,max);
			} else {
				return new JFuzzInterval(interval.type,interval.min,upper.getValue());
			}
		} else {
			if (lower.isFinite()) {
				return new JFuzzInterval(interval.type,lower.getValue(),interval.max);
			} else {
				return interval;
			}
		}
	}
	
}
