/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.lustre.generalize;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import fuzzm.lustre.evaluation.DepthFirstSimulator;
import fuzzm.lustre.evaluation.EvaluatableArgList;
import fuzzm.lustre.evaluation.FunctionLookupEV;
import fuzzm.lustre.evaluation.PolyFunctionLookup;
import fuzzm.lustre.evaluation.PolyFunctionMap;
import fuzzm.poly.PolyBase;
import fuzzm.poly.PolyBool;
import fuzzm.poly.VariableID;
import fuzzm.util.Debug;
import fuzzm.util.ID;
import fuzzm.util.Rat;
import fuzzm.util.TypedName;
import fuzzm.value.hierarchy.EvaluatableValue;
import fuzzm.value.hierarchy.InstanceType;
import fuzzm.value.poly.BooleanPoly;
import fuzzm.value.poly.GlobalState;
import fuzzm.value.poly.IntegerPoly;
import fuzzm.value.poly.PolyEvaluatableValue;
import fuzzm.value.poly.RationalPoly;
import jkind.lustre.BinaryExpr;
import jkind.lustre.BinaryOp;
import jkind.lustre.BoolExpr;
import jkind.lustre.CastExpr;
import jkind.lustre.Expr;
import jkind.lustre.FunctionCallExpr;
import jkind.lustre.IdExpr;
import jkind.lustre.IfThenElseExpr;
import jkind.lustre.IntExpr;
import jkind.lustre.NamedType;
import jkind.lustre.Program;
import jkind.lustre.RealExpr;
import jkind.lustre.Type;
import jkind.lustre.values.Value;
import jkind.util.BigFraction;

public class DepthFirstPolyGeneralizer extends DepthFirstSimulator {

	final PolyFunctionLookup ftable;
	final PolyFunctionMap    fmap;
	
	public DepthFirstPolyGeneralizer(FunctionLookupEV fns, Program prog) {
		super(fns,prog);
		ftable = new PolyFunctionLookup(fns.fsig);
		fmap   = new PolyFunctionMap();
		addGlobalUFInvariants(fns);
	}
	
	static List<PolyEvaluatableValue> nthArgs(int n, Collection<EvaluatableArgList> args) {
		List<PolyEvaluatableValue> res = new ArrayList<>();
		for (EvaluatableArgList inst: args) {
			res.add((PolyEvaluatableValue) inst.get(n));
		}
		return res;
	}
	
	private void orderInvariants(NamedType type, List<PolyEvaluatableValue> nth) {
		if (nth.size() > 1) {
			PolyEvaluatableValue prev = nth.get(0);
			for (int index = 1; index<nth.size(); index++) {
				PolyEvaluatableValue curr = nth.get(index);
				int sign = prev.compareTo(curr);
				BooleanPoly res = BooleanPoly.TRUE;
				if (type == NamedType.BOOL) {
					res = (BooleanPoly) prev.implies(curr);
				} else {
					if (sign == 0) {
						res = (BooleanPoly) prev.lessequal(curr);						
					} else {
						res = (BooleanPoly) prev.less(curr);
					}
				}
				GlobalState.addConstraint(res.value);
				prev = curr;
			}	
		}
	}
	
	private void addGlobalUFInvariants(FunctionLookupEV fns) {
		for (String fn: fns.keySet()) {
			for (EvaluatableArgList args: fns.getInstances(fn)) {
				BigFraction fnValue = ((InstanceType<?>) fns.get(fn, args)).getValue();
				String prefix = "UF_" + fn +  args.toString();
				String fnvarname = prefix + ".cex = " + fnValue;
				VariableID fnvar = VariableID.postAlloc(fnvarname,fns.fsig.getFnType(fn),fnValue);
				ftable.setFnValue(fn, args, fnvar);
				List<VariableID> argv = new ArrayList<>();
				List<TypedName> argvars = new ArrayList<>();
				int index = 0;
				for (EvaluatableValue arg: args) {
					BigFraction argValue = ((InstanceType<?>) arg).getValue();
					String base = prefix + "_arg" + index + ".cex = " + argValue ;
					VariableID z = VariableID.postAlloc(base,fns.fsig.getArgTypes(fn).get(index),argValue);
					argvars.add(z.name.name);
					argv.add(z);
					index++;
				}
				ftable.setArgValues(fn, args, argv);
				fmap.updateFnMap(fn, argvars, fnvar.name.name);		
			}
		}
		for (String fn: fns.keySet()) {
			List<NamedType> argtypes = ftable.getArgTypes(fn);
			if (Debug.isEnabled()) System.out.println(ID.location() + "Adding " + fn + " argument order invariants .. ");							
			for (int index = 0; index<argtypes.size(); index++) {
				List<PolyEvaluatableValue> nth = ftable.getFnNthArgs(fn,index);
				Collections.sort(nth);
				// From smallest to largest ..
				orderInvariants(argtypes.get(index),nth);
			}
			// No need to constrain UF outputs ..
			//System.out.println(ID.location() + "Adding " + fn + " value order invariants .. ");
			//List<PolyEvaluatableValue> values = ftable.getFnValues(fn);
			//Collections.sort(values);
			//orderInvariants(ftable.getFnType(fn),values);
		}
		if (Debug.isEnabled()) System.out.println(ID.location() + "Function Table:");
		if (Debug.isEnabled()) System.out.println(ftable.toString());
	}
	
	@Override
	public Value visit(IfThenElseExpr e) {
		Expr testExpr = e.cond;
		Expr thenExpr = e.thenExpr;
		Expr elseExpr = e.elseExpr;
		Value res;
		BooleanPoly testValue = (BooleanPoly) testExpr.accept(this);
		if (testValue.isAlwaysTrue()) {
			res = thenExpr.accept(this);
		} else if (testValue.isAlwaysFalse()) {
			res = elseExpr.accept(this);
		} else {
			Type et = typeOf(thenExpr);
			if (et == NamedType.BOOL) {
				EvaluatableValue thenValue = (EvaluatableValue) thenExpr.accept(this);
				EvaluatableValue elseValue = (EvaluatableValue) elseExpr.accept(this);
				res = testValue.ite(thenValue,elseValue);
			} else {
				PolyBool tv = testValue.value;
				if (tv.cex) {
					GlobalState.addConstraint(tv);
					res = thenExpr.accept(this);
				} else {
					GlobalState.addConstraint(tv.not());
					res = elseExpr.accept(this);
				}
			}
		}
		return res;
	}
	
	@Override
	public EvaluatableValue visit(IntExpr arg0) {
		return new IntegerPoly(new PolyBase(new BigFraction(arg0.value)));
	}

	@Override
	public EvaluatableValue visit(RealExpr arg0) {
		return new RationalPoly(new PolyBase(BigFraction.valueOf(arg0.value)));
	}

	@Override
	public EvaluatableValue visit(BoolExpr arg0) {
		return arg0.value ? new BooleanPoly(PolyBool.TRUE) : new BooleanPoly(PolyBool.FALSE);
	}

	@Override
	public EvaluatableValue visit(CastExpr e) {
	    EvaluatableValue arg = (EvaluatableValue) e.expr.accept(this);
	    GlobalState.pushExpr(step, e);
	    EvaluatableValue res = arg.cast(e.type);
	    Expr r = GlobalState.popExpr();
        assert(r == e);
	    return res;
	}	    

	@Override
	public Value visit(BinaryExpr e) {
	    if (e.op == BinaryOp.INT_DIVIDE) {
	        EvaluatableValue L = (EvaluatableValue) e.left.accept(this);
	        EvaluatableValue R = (EvaluatableValue) e.right.accept(this);
	        GlobalState.pushExpr(step, e);
	        Value res = L.int_divide(R);
	        Expr r = GlobalState.popExpr();
	        assert(r == e);
	        return res;
	    } else if (e.op == BinaryOp.MODULUS){
	        EvaluatableValue L = (EvaluatableValue) e.left.accept(this);
	        EvaluatableValue R = (EvaluatableValue) e.right.accept(this);
	        GlobalState.pushExpr(step, e);
	        Value res = L.modulus(R);
	        Expr r = GlobalState.popExpr();
	        assert(r == e);
	        return res;
	    } else {
	        return super.visit(e);
	    }
	}
	@Override
	public EvaluatableValue visit(FunctionCallExpr e) {
        String fn = e.function;
		List<EvaluatableValue> polyArgs = new ArrayList<>();
		EvaluatableArgList cexArgs = new EvaluatableArgList();
		List<NamedType> argtypes = ftable.getArgTypes(e.function);
		int index = 0;
		for (Expr v: e.args) {
			PolyEvaluatableValue ev = (PolyEvaluatableValue) v.accept(this);
			polyArgs.add(ev);
			cexArgs.add(Rat.ValueFromTypedFraction(argtypes.get(index), ev.cex()));
			index++;
		}
		List<VariableID> ufVarArgs = ftable.getArgVarValues(fn,cexArgs);
		index = 0;
        for (Expr v: e.args) {
		    GlobalState.addReMap(ufVarArgs.get(index), step, v);
		    index++;
		}
		// From the function name and the arguments we can get
		// the poly args and the poly return value.
		List<PolyEvaluatableValue> ufPolyArgs = ftable.getArgPolyValues(fn,cexArgs);
		PolyEvaluatableValue ufPolyValue = ftable.getFnPolyValue(fn, cexArgs);
		index = 0;
		for (EvaluatableValue v: polyArgs) {
			BooleanPoly res = (BooleanPoly) v.equalop(ufPolyArgs.get(index));
			if (Debug.isEnabled()) System.out.println(ID.location() + "Adding " + e.function + " Instance Constraint");
			GlobalState.addConstraint(res.value);
			index++;
		}
		if (Debug.isEnabled()) System.out.println(ID.location() + e + " evaluated to " + ufPolyValue + " [" + ufPolyValue.cex() + "]");
		GlobalState.addReMap(ftable.getFnVarValue(fn,cexArgs), step, e);
		return ufPolyValue;
	}

	@Override
	protected PolyEvaluatableValue getDefaultValue(IdExpr e) {
		Type type = types.get(e.id);
		if (type == NamedType.BOOL) {
			return BooleanPoly.FALSE;
		}
		if (type == NamedType.INT) {
			return new IntegerPoly(new PolyBase());
		}
		if (type == NamedType.REAL) {
			return new RationalPoly(new PolyBase());
		}
		throw new IllegalArgumentException();
	}
	
}
