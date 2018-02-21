/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.poly;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import fuzzm.lustre.SignalName;
import fuzzm.lustre.evaluation.PolyFunctionMap;
import fuzzm.solver.SolverResults;
import fuzzm.util.FuzzMInterval;
import fuzzm.util.ID;
import fuzzm.util.IntervalVector;
import fuzzm.util.Rat;
import fuzzm.util.RatSignal;
import fuzzm.util.RatVect;
import fuzzm.util.TypedName;
import fuzzm.value.instance.RationalValue;
import fuzzm.value.poly.GlobalState;
import jkind.lustre.NamedType;
import jkind.util.BigFraction;

public class VariableList extends LinkedList<Variable> {

	private static final long serialVersionUID = 7983100382771154597L;
	
	public VariableList() {
		super();
	}
	
	public VariableList(VariableList arg) {
		super(arg);
	}
	
	public VariableList(Variable c) {
		super();
		addLast(c);
	}
	
//	public VariableList not() {
//		VariableList res = new VariableList();
//		for (Variable vc: this) {
//			res.addLast(vc.not());
//		}
//		return res;
//	}
	
	@Override
	public boolean add(Variable b) {
		throw new IllegalArgumentException();
	}
	
	public static void printAddFirst(String alt, Variable b, Variable first) {
		System.out.println("addFirst"+alt+"("+b.vid+":"+b.vid.level()+","+first.vid+":"+first.vid.level() + ",...)");
	}
	
	public static void printAddLast(String alt, Variable last, Variable b) {
		System.out.println("addLast"+alt+"(...,"+last.vid+":"+last.vid.level()+","+b.vid+":"+b.vid.level()+")");
	}
	
	@Override
	public void addFirst(Variable b) {
		// Maintain the ordering invariant ..
		if (! isEmpty()) {
			if (b.vid.compareTo(this.peekFirst().vid) >= 0) {
				printAddFirst("",b,this.peekFirst());				
				throw new IllegalArgumentException();
			}
		}
		super.addFirst(b);
	}
	
	@Override
	public void addLast(Variable b) {
		// Maintain the ordering invariant ..
		if (! isEmpty()) {
			if (this.peekLast().vid.compareTo(b.vid) >= 0) {
				printAddLast("",this.peekLast(),b);
				throw new IllegalArgumentException();
			}
		}
		super.addLast(b);
	}
	
	public void addFirstRev(Variable b) {
		// Maintain the ordering invariant ..
		if (! isEmpty()) {
			if (b.vid.compareTo(this.peekFirst().vid) <= 0) {
				printAddFirst("Rev",b,this.peekFirst());				
				throw new IllegalArgumentException();
			}
		}
		super.addFirst(b);
	}
	
	public void addLastRev(Variable b) {
		// Maintain the ordering invariant ..
		if (! isEmpty()) {
			if (this.peekLast().vid.compareTo(b.vid) <= 0) {
				printAddLast("Rev",this.peekLast(),b);
				throw new IllegalArgumentException();
			}
		}
		super.addLast(b);
	}

	   public static VariableList andTF(VariableList x, VariableList y) {
	        // andTF: Here T and F refer to the polarity of the associated
	        // polyBool.  y is, therefore, an implicitly negated 'or'
	        // expression.  We will be discarding all of x.
	        if (x.isEmpty()) return y;
	        if (y.isEmpty()) return y;
	        VariableList res = new VariableList();
	        Iterator<Variable> xit = x.iterator();
	        Iterator<Variable> yit = y.iterator();
	        Variable xv = xit.next();
	        Variable yv = yit.next();
	        while (true) {
	            int cmp = xv.vid.compareTo(yv.vid);
	            if (cmp > 0) {
	                res.addLast(yv);
	                if (! yit.hasNext()) {
	                    res.addLast(new VariablePhantom(xv));
	                    break;
	                }
	                yv = yit.next();
	            } else if (cmp < 0){
	                res.addLast(new VariablePhantom(xv));
	                if (! xit.hasNext()) {
	                    res.addLast(yv);
	                    break;
	                }
	                xv = xit.next();
	            } else {
	                Variable z = Variable.target(yv,false,xv,true);
	                res.addLast(z);
	                if (! (xit.hasNext() && yit.hasNext())) break;
	                xv = xit.next();
	                yv = yit.next();
	            }
	        }
	        while (yit.hasNext()) {
	            res.addLast(yit.next());
	        }
	        return res;
	    }
	
	public static VariableList andFF(VariableList x, VariableList y) {
	    // andFF: So we have the option of choosing one or the other
	    // or of conjoining both.  One might argue that, to keep the
	    // solution space as large as possible, one should simply
	    // discard one list or the other.  However, when we consider
	    // sampling, the false space gives us information about which
	    // constraints to TARGET.
        if (x.isEmpty()) return y;
        if (y.isEmpty()) return x;
        VariableList res = new VariableList();
        Iterator<Variable> xit = x.iterator();
        Iterator<Variable> yit = y.iterator();
        Variable xv = xit.next();
        Variable yv = yit.next();
        while (true) {
            int cmp = xv.vid.compareTo(yv.vid);
            if (cmp > 0) {
                res.addLast(yv);
                if (! yit.hasNext()) {
                    res.addLast(xv);
                    break;
                }
                yv = yit.next();
            } else if (cmp < 0){
                res.addLast(xv);
                if (! xit.hasNext()) {
                    res.addLast(yv);
                    break;
                }
                xv = xit.next();
            } else {
                Variable z = Variable.minSet(xv,yv);
                res.addLast(z);
                if (! (xit.hasNext() && yit.hasNext())) break;
                xv = xit.next();
                yv = yit.next();
            }
        }
        while (xit.hasNext()) {
            res.addLast(xit.next());
        }
        while (yit.hasNext()) {
            res.addLast(yit.next());
        }
        return res;
	}
	
	
	public static VariableList andTT(VariableList x, VariableList y) {
		if (x.isEmpty()) return y;
		if (y.isEmpty()) return x;
		VariableList ctx = new VariableList();
        Iterator<Variable> xit = x.iterator();
		Iterator<Variable> yit = y.iterator();
		Variable xv = xit.next();
		Variable yv = yit.next();
		//System.out.println("and() ..");
		while (true) {
			//System.out.println("xv:" + xv.vid + ":" + xv.vid.level());
			//System.out.println("yv:" + yv.vid + ":" + yv.vid.level());
			int cmp = xv.vid.compareTo(yv.vid);
			// Normal list is ordered from smallest to largest.
			if (cmp > 0) {
				// x is greater than y ..
				//if (Debug.isEnabled()) System.out.println(ID.location() + "(T and " + yv + ") = " + yv);
				ctx.addFirstRev(yv);
				if (! yit.hasNext()) {
					ctx.addFirstRev(xv);
					break;
				}
				yv = yit.next();
			} else if (cmp < 0){
				ctx.addFirstRev(xv);
				//if (Debug.isEnabled()) System.out.println(ID.location() + "(" + xv + " and T) = " + xv);
				if (! xit.hasNext()) {
					ctx.addFirstRev(yv);
					break;
				}
				xv = xit.next();
			} else {
			    RestrictionResult rr = Variable.andTrue(xv,yv);
			    //if (Debug.isEnabled()) System.out.println(ID.location() + "(" + xv + " and " + yv + ") = " + rr.newConstraint);
			    for (Variable r: rr.restrictionList) {
			        ctx = restrict(r,ctx.iterator());
			    }
			    ctx.addFirstRev(rr.newConstraint);
				if (! (xit.hasNext() && yit.hasNext())) break;
				xv = xit.next();
				yv = yit.next();
			}
		}
		while (xit.hasNext()) {
			ctx.addFirstRev(xit.next());
		}
		while (yit.hasNext()) {
			ctx.addFirstRev(yit.next());
		}
		Collections.reverse(ctx);
		//System.out.println("and().");
		return ctx;
	}
	
	public static VariableList restrict(Variable c, Iterator<Variable> xit) {
		//System.out.println("Push " + c.vid + ":" + c.vid.level() + " ..");
		//if (Debug.isEnabled()) System.out.println(ID.location() + "Restriction : " + c);
		VariableList res = new VariableList();
		while (xit.hasNext()) {
			// Reversed list is ordered from largest to smallest
			Variable xv = xit.next();
			//System.out.println("Restriction : " + c.vid+":"+c.vid.level());
			//System.out.println("Location    : " + xv.vid+":"+xv.vid.level());
			int cmp = xv.vid.compareTo(c.vid);
			if (cmp > 0) {
				res.addLastRev(xv);
			} else {
				if (cmp < 0) {
					res.addLastRev(c);
					c = xv;
				} else {
					RestrictionResult rr = Variable.andTrue(xv,c);
					//if (Debug.isEnabled()) System.out.println(ID.location() + "("+xv+" ^ "+c+") = " + rr.newConstraint);
					for (Variable vc: rr.restrictionList) {
						VariableList pres = restrict(vc,xit);
						xit = pres.iterator();
					}
					c = rr.newConstraint;
				}
				while (xit.hasNext()) {
					res.addLastRev(c);
					c = xit.next();
				}
			}
		}
		res.addLastRev(c);
		//System.out.println("Pop.");
		return res;
	}
	
	public VariableList applyRewrites() {
		Map<VariableID,AbstractPoly> rewrite = new HashMap<>();
		VariableList res = new VariableList();
		for (Variable v: this) {
			v = v.rewrite(rewrite);
			boolean keep = true;
			if (v instanceof VariableEquality) {				
				VariableEquality veq = (VariableEquality) v;
				if (veq.relation == RelationType.INCLUSIVE) {
					rewrite.put(veq.vid, veq.poly);
					keep = (veq.vid.role != VariableRole.AUXILIARY);
				}
			}
			if (keep) res.addLast(v);
		}
		return res;
	}
	
	public VariableList normalize() {
		VariableList x = this.applyRewrites();
		boolean changed;
		do {
			changed = false;
			x = new VariableList(x);
			Collections.reverse(x);
			VariableList res = new VariableList();
			while (! x.isEmpty()) {
				//System.out.println(ID.location() + "Generalization size : " + x.size());
				//System.out.println(ID.location() + x);
				Variable v = x.poll();
				if (v instanceof VariablePhantom) {
				    continue;
				}
				if (v.implicitEquality()) {
					//System.out.println(ID.location() + "Implicit Equality : " + v);
					v = v.toEquality();
					changed = true;
				}
				if (v.slackIntegerBounds()) {
					//System.out.println(ID.location() + "Slack Bounds : " + v);
					v = v.tightenIntegerBounds();
					changed = true;
				}
				if (v.reducableIntegerInterval()) {
					//System.out.println(ID.location() + "reducableIntegerInterval : " + v);
					RestrictionResult er = v.reducedInterval();
					//System.out.println(ID.location() + "reducedInterval : " + er);
					v = er.newConstraint;
					for (Variable r: er.restrictionList) {
						x = restrict(r,x.iterator());
					}
					changed = true;
				}
				if (v.requiresRestriction()) {
					RestrictionResult rr = v.restriction();
					v = rr.newConstraint;
					for (Variable r: rr.restrictionList) {
						x = restrict(r,x.iterator());
					}
				}
				res.addFirst(v);
			}
			x = res.applyRewrites();
		} while (changed);
		return x;
	}
	
//	public VariableList chooseAndNegateOne() {
//		Variable one = null;
//		int max = 0;
//		for (Variable v : this) {
//			if (v.countFeatures() >= max) {
//				one = v;
//				max = v.countFeatures();
//			}
//		}
//		assert(one != null);
//		return new VariableList(one.not());
//	}

	public RatSignal randomVector(boolean biased, BigFraction Smin, BigFraction Smax, IntervalVector span, Map<VariableID,BigFraction> ctx) {
		//int tries = 100;
	    @SuppressWarnings("unused")
        int bools = 0;
	    while (true) {
			try {
				RatSignal res = new RatSignal();
				for (Variable c: this) {
					RegionBounds r;
					try {
						r = c.constraintBounds(ctx);
					} catch (EmptyIntervalException e) {
						System.out.println(ID.location() + "Constraint : " + c);
						System.out.println(ID.location() + "Context : " + ctx);
						throw new IllegalArgumentException();
					}
					VariableID vid = c.vid;
					SignalName sn  = vid.name;
					TypedName  name = sn.name;
					NamedType type = c.vid.name.name.type;
					FuzzMInterval bounds;
					try {
						bounds = span.containsKey(name) ? r.fuzzInterval(span.get(name)) : r.fuzzInterval(type, Smin, Smax);			
					} catch (EmptyIntervalException e) {
						System.out.println(ID.location() + "Constraint : " + c);
						System.out.println(ID.location() + "Context : " + ctx);
						System.out.println(ID.location() + "RegionBounds : " + r);
						throw new IllegalArgumentException();
					}
					BigFraction value;
					if (r.rangeType == RelationType.INCLUSIVE) {				
						try {
							value = Rat.biasedRandom(type, biased, 0, bounds.min, bounds.max);		
						} catch (EmptyIntervalException e) {
							System.out.println(ID.location() + "Constraint : " + c);
							System.out.println(ID.location() + "CEX String : " + c.cexString());
							System.out.println(ID.location() + "Context : " + ctx);
							System.out.println(ID.location() + "RegionBounds : " + r);
							System.out.println(ID.location() + "FuzzMBounds  : " + bounds);
							throw new IllegalArgumentException();
						}
					} else {
						BigFraction upper = ((RationalValue) r.upper).value();
						BigFraction lower = ((RationalValue) r.lower).value();
						BigFraction one   = type == NamedType.INT ? BigFraction.ONE : BigFraction.ZERO;
						BigFraction max = bounds.max.add(lower.subtract(bounds.min)).add(one);
						value = Rat.biasedRandom(type, biased, 0, upper, max);
					}
					if (sn.time >= 0) res.put(sn.time, sn.name, value);
					ctx.put(vid, value);
					if (! c.evalCEX(ctx)) {
						System.out.println(ID.location() + "Constraint : " + c);
						System.out.println(ID.location() + "Context : " + ctx);
						System.out.println(ID.location() + "RegionBounds : " + r);
						System.out.println(ID.location() + "FuzzMBounds  : " + bounds);
						assert(false);
					}
				}
				// We should probably do this for all the variable types ..
				for (TypedName z : span.keySet()) {
					for (RatVect rv: res) {
						if (! rv.containsKey(z)) {
						    if (z.type == NamedType.BOOL) {
						        rv.put(z, GlobalState.oracle().nextBoolean() ? BigFraction.ONE : BigFraction.ZERO);
							} else {
							    rv.put(z, Rat.biasedRandom(z.type, biased, 0, span.get(z).min, span.get(z).max));
							}
						}
					}
				}
				//System.out.println(ID.location() + "Vector : "+ res);
				return res;
			} catch (EmptyIntervalException e) {
				throw new IllegalArgumentException(e);
//				tries--;
//				if (tries <= 0) throw e;
//				continue;
			}
		}
	}

	public Collection<VariableID> unboundVariables() {
		Set<VariableID> bound = new HashSet<>();		
		Set<VariableID> used  = new HashSet<>();
		for (Variable v: this) {
			bound.add(v.vid);
		}
		for (Variable v: this) {
			used = v.updateVariableSet(used);
		}
		used.removeAll(bound);
		return used;
	}
	
	public Map<VariableID,RegionBounds> intervalBounds() {
		Map<VariableID,RegionBounds> res = new HashMap<>();
		for (Variable v: this) {
			RegionBounds b = v.intervalBounds(res);
			res.put(v.vid, b);
		}
		return res;
	}

	public SolverResults optimize(SolverResults sln, PolyFunctionMap fmap, RatSignal target) {
		RatSignal res = new RatSignal(sln.cex);
		RatVect tempVars = new RatVect();
		VariableList z = new VariableList(this);
		// We need to do this top to bottom.
        Collections.reverse(z);
		while (! z.isEmpty()) {
		    Variable v = z.poll();
			RegionBounds interval;
			BigFraction value; 
			if (v instanceof VariablePhantom) continue;
			if (v instanceof VariableBoolean) {
			    value = v.vid.cex;
			    int time = v.vid.name.time;
                TypedName tname = v.vid.name.name;
                if (time >= 0) {
                    res.put(v.vid.name.time,v.vid.name.name,value);
                } else {
                    tempVars.put(tname, value);
                }
			} else {
			    try {
			        interval = v.constraintBounds().fix(v.vid.name.name.type);
			    } catch (EmptyIntervalException e) {
			        System.out.println(ID.location() + "Interval Bound Violation on " + v);
			        throw e;
			    }
			    int time = v.vid.name.time;
			    TypedName tname = v.vid.name.name;
			    NamedType type = v.vid.name.name.type;
			    // TODO: Using only variable type I think we want to differentiate between
			    // variables that map back into the model and those that do not.  Here, 
			    // especially, we want to know the variables used in UF generalization.
			    if (time >= 0) {
			        value = interval.optimize(type,target.get(time).get(tname));
			        res.put(v.vid.name.time,v.vid.name.name,value);
			    } else {
			        // You could use a random value here .. because what we are doing is kinda silly.
			        // Or just leave it unconstrained.
			        value = interval.optimize(type, v.vid.getCex());
			        tempVars.put(tname, value);
			    }
			    // Now restrict the remaining constraints so that 
			    // they always at least contain "value"
			    RestrictionResult rr = v.mustContain(new PolyBase(value));
                v = rr.newConstraint;
                for (Variable r: rr.restrictionList) {
                    z = restrict(r,z.iterator());
                }
			}
			// assert(v.evalCEX(ctx)) : "Failure to preserve " + v + " with " + value + " under " + ctx;
		}
		fmap.updateFunctions(tempVars, sln.fns);
		return new SolverResults(sln.time,res,sln.fns);		
	}
	
	public int[] gradiantToDirectionMatrix(AbstractPoly gradiant) {
		int direction[] = new int[this.size()];
		Iterator<Variable> it = this.descendingIterator();
		int index = this.size();
		while (it.hasNext()) {
			index--;
			Variable v = it.next();
			int sign = gradiant.getCoefficient(v.vid).signum();
			direction[index] = sign;
			AbstractPoly bound = v.maxBound(sign);
			gradiant = gradiant.remove(v.vid);
			BigFraction N = gradiant.dot(bound);
			BigFraction D = bound.dot(bound);
			gradiant = gradiant.subtract(bound.divide(N.divide(D)));
			if (gradiant.isConstant()) break;
		}
		while (it.hasNext()) {
			index--;
			it.next();
			direction[index] = 1;
		}
		assert(index == 0);
		return direction;
	}
	
	public Map<VariableID,BigFraction> maximize(int direction[]) {
		int index = 0;
		Map<VariableID,BigFraction> ctx = new HashMap<>();
		for (Variable v: this) {
			BigFraction value = v.maxValue(direction[index], ctx);
			ctx.put(v.vid, value);
			index++;
		}
		return ctx;
	}

    public List<Variable> getTargets() {
        List<Variable> res = new ArrayList<>(); 
        for (Variable v: this) {
            if (v instanceof VariableInterval) {
                VariableInterval vi = (VariableInterval) v;
                if (vi.gt.isTarget()) res.add(vi.gt);
                if (vi.lt.isTarget()) res.add(vi.lt);                                
            } else if (v.isTarget()) {
                res.add(v);                    
            }
        }
        return res;
    }

    public List<Variable> getArtifacts() {
        List<Variable> res = new ArrayList<>(); 
        for (Variable v: this) {
            if (v instanceof VariableInterval) {
                VariableInterval vi = (VariableInterval) v;
                if (vi.gt.isArtifact()) res.add(vi.gt);
                if (vi.lt.isArtifact()) res.add(vi.lt);                                
            } else if (v.isArtifact()) {
                res.add(v);                    
            }
        }
        return res;
    }

}
