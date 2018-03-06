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
import java.util.List;

import fuzzm.value.poly.GlobalState;
import jkind.util.BigFraction;

abstract public class VariableBound extends Variable {

	public VariableBound(VariableID vid, boolean cex) {
		super(vid,cex);
	}
	
	static RestrictionResult restrictInequalityGradient(AbstractPoly gradient, VariableInequality x, VariableInequality y) {
		BigFraction xg = gradient.dot(x.poly);
		BigFraction yg = gradient.dot(y.poly);
		int cmp = xg.compareTo(yg);
		if (cmp == 0) {
			cmp = x.poly.remove(gradient).compareTo(y.poly.remove(gradient));
		}
		return restrictInequalityAux(cmp > 0,x,y);
	}

	// ACL2: (def::trueAnd restrictInequality (x y cex)
	static RestrictionResult restrictInequality(VariableInequality x, VariableInequality y) {
		int fcmp = x.countFeatures() - y.countFeatures();
		boolean choosex = ((fcmp > 0) || ((fcmp == 0) && GlobalState.oracle().nextBoolean()));
		return restrictInequalityAux(choosex,x,y);
	}
	
	static RestrictionResult restrictInequalityAux(boolean prefx, VariableInequality x, VariableInequality y) {
		assert(x.cex && y.cex);
		assert(x.vid.equals(y.vid));
		AbstractPoly diff = (x instanceof VariableGreater) ? y.poly.subtract(x.poly) :
								x.poly.subtract(y.poly);
		int cmp = diff.evaluateCEX().signum();				
		int xcmp = x.relation.compareWith(y.relation);
		boolean choosex = ((cmp < 0) ||
				            ((cmp == 0) && 
				        	  ((xcmp < 0) || 
				                ((xcmp == 0) && prefx))));
		VariableInequality keep;
		TargetType newTarget = x.target.inherit(y.target);
		if (choosex) {
			keep = x;
			diff = diff.negate();
		} else {
			keep = y;
		}
		if (diff.isConstant()) {
			return new RestrictionResult(keep.setTarget(newTarget));
		}
		RelationType relation = RelationType.INCLUSIVE;
		if ((xcmp != 0) && (keep.relation == RelationType.INCLUSIVE)) {
			relation = RelationType.EXCLUSIVE;
		}
		return new RestrictionResult(keep,solvePolyGreater0(diff,relation,true,FeatureType.NONFEATURE,newTarget));
	}

    static VariableEquality solvePolyEquality0(AbstractPoly arg, FeatureType feature, TargetType target) {
        assert(arg.evaluateCEX().signum() == 0);
        VariableID id = arg.leadingVariable();
        AbstractPoly poly = arg.solveFor(id);
        return new VariableEquality(id,true,poly,feature, target);
    }
    
	static PolyBool normalizePolyEquality0(AbstractPoly arg, FeatureType feature, TargetType target) {
	    VariableID id = arg.leadingVariable();
	    AbstractPoly  poly = arg.solveFor(id);
	    // x = -poly
	    BigFraction diff = poly.evaluateCEX().subtract(id.cex);
	    int cmp = diff.signum();
	    VariableBound res;
	    if (cmp == 0) {
	        return new TruePolyBool(new VariableEquality(id,true,poly,feature, target));
	    } else if (cmp < 0) {
            res = new VariableGreater(id,true,RelationType.EXCLUSIVE,poly,feature,target);
        } else {
            res = new VariableLess(id,true,RelationType.EXCLUSIVE,poly,feature,target);
        }
        return new TruePolyBool(res).not();
        // else {
	    //    poly = poly.subtract(diff);
	    //    return new FalsePolyBool(new VariableEquality(id,true,poly,feature, target));
	    //}
	}
	
    static PolyBool normalizePolyGreater0(AbstractPoly arg, RelationType relation, FeatureType feature, TargetType target) {
        if (relation.gt(arg.evaluateCEX().signum())) {
            return new TruePolyBool(solvePolyGreater0(arg, relation, true, feature, target));
        }
        return new TruePolyBool(solvePolyLess0(arg, relation.not(), true, feature, target)).not();
    }
    
    static PolyBool normalizePolyLess0(AbstractPoly arg, RelationType relation, FeatureType feature, TargetType target) {
        if (relation.lt(arg.evaluateCEX().signum())) {
            return new TruePolyBool(solvePolyLess0(arg, relation, true, feature, target));
        }
        return new TruePolyBool(solvePolyGreater0(arg, relation.not(), true, feature, target)).not();
    }
    
	// ACL2 : (def::un solvePolyGreater0 (relation poly)
	static VariableInequality solvePolyGreater0(AbstractPoly poly, RelationType relation, boolean cex, FeatureType feature, TargetType target) {
	    assert(cex && relation.gt(poly.evaluateCEX().signum()));
		//
		// Normalizes an expression of the form (<~ 0 poly)
		//
		VariableID name = poly.leadingVariable();
		int sign = poly.getCoefficient(name).signum();
		AbstractPoly sln = poly.solveFor(name);
		VariableInequality r = (sign < 0) ? new VariableLess(name,cex,relation,sln,feature,target) :
				                            new VariableGreater(name,cex,relation,sln,feature,target);			                                
		//if (Debug.isEnabled()) System.out.println(ID.location() + "(< 0 " +  poly + ") = " + r);
		return r;
	}

	// ACL2 : (def::un solvePolyLess0 (relation poly)
	static VariableInequality solvePolyLess0(AbstractPoly poly, RelationType relation, boolean cex, FeatureType feature, TargetType target) {
		return solvePolyGreater0(poly.negate(),relation,cex,feature,target);
	}

	// ACL2: (def::un restrictDisequality (xpoly ypoly relation cex)
	static List<Variable> restrictDisequality(AbstractPoly xpoly, AbstractPoly ypoly, RelationType relation, TargetType target) {
		// If you already know the relation and which variable bound to keep ..
		List<Variable> res = new ArrayList<>();
		//if (Debug.isEnabled()) System.out.println(ID.location() + "restrictX: " + x + " & " + y);
		AbstractPoly diff = xpoly.subtract(ypoly);
		if (diff.isConstant()) {
			return res;
		}
		BigFraction z = diff.evaluateCEX();
		int cmp = z.signum();
		diff = (0 < cmp) ? diff : diff.negate();
		if (! (diff.evaluateCEX().signum() >= 0)) 
			assert(false);
		res.add(solvePolyGreater0(diff,relation,true,FeatureType.NONFEATURE,target));
		return res;
	}

	
}
