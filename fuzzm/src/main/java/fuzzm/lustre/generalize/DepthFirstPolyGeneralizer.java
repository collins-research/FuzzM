package jfuzz.lustre.generalize;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import jfuzz.lustre.evaluation.DepthFirstSimulator;
import jfuzz.lustre.evaluation.EvaluatableArgList;
import jfuzz.lustre.evaluation.FunctionLookupEV;
import jfuzz.lustre.evaluation.PolyFunctionLookup;
import jfuzz.lustre.evaluation.PolyFunctionMap;
import jfuzz.poly.PolyBase;
import jfuzz.poly.PolyBool;
import jfuzz.poly.VariableID;
import jfuzz.util.Debug;
import jfuzz.util.ID;
import jfuzz.util.Rat;
import jfuzz.util.TypedName;
import jfuzz.value.hierarchy.EvaluatableValue;
import jfuzz.value.hierarchy.InstanceType;
import jfuzz.value.poly.BooleanPoly;
import jfuzz.value.poly.GlobalState;
import jfuzz.value.poly.IntegerPoly;
import jfuzz.value.poly.PolyEvaluatableValue;
import jfuzz.value.poly.RationalPoly;
import jkind.lustre.BoolExpr;
import jkind.lustre.Expr;
import jkind.lustre.FunctionCallExpr;
import jkind.lustre.IdExpr;
import jkind.lustre.IfThenElseExpr;
import jkind.lustre.IntExpr;
import jkind.lustre.NamedType;
import jkind.lustre.Node;
import jkind.lustre.RealExpr;
import jkind.lustre.Type;
import jkind.lustre.values.Value;
import jkind.util.BigFraction;

public class DepthFirstPolyGeneralizer extends DepthFirstSimulator {

	final PolyFunctionLookup ftable;
	final PolyFunctionMap    fmap;
	
	public DepthFirstPolyGeneralizer(FunctionLookupEV fns, Node node) {
		super(fns,node);
		ftable = new PolyFunctionLookup(fns.fsig);
		fmap   = new PolyFunctionMap();
		addGlobalUFInvariants(fns);
	}
	
	static PolyEvaluatableValue toPEV(NamedType type, VariableID varid) {
		if (type == NamedType.BOOL) {
			return (varid.cex.compareTo(BigFraction.ZERO) == 0) ? BooleanPoly.FALSE : BooleanPoly.TRUE;
		}
		if (type == NamedType.INT) {
			return new IntegerPoly(varid);
		}
		if (type == NamedType.REAL) {
			return new RationalPoly(varid);
		}
		throw new IllegalArgumentException();
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
				String fnvarname = prefix + "=" + fnValue;
				VariableID fnvar = VariableID.postAlloc(fnvarname,fns.fsig.getFnType(fn),fnValue);
				ftable.setFnValue(fn, args, toPEV(fns.fsig.getFnType(fn),fnvar));
				List<PolyEvaluatableValue> argv = new ArrayList<>();
				List<TypedName> argvars = new ArrayList<>();
				int index = 0;
				for (EvaluatableValue arg: args) {
					BigFraction argValue = ((InstanceType<?>) arg).getValue();
					String base = prefix + "_arg" + index;
					VariableID z = VariableID.postAlloc(base,fns.fsig.getArgTypes(fn).get(index),argValue);
					argvars.add(z.name.name);
					PolyEvaluatableValue w = toPEV(fns.fsig.getArgTypes(fn).get(index),z);
					argv.add(w);
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
		if (testValue.isTrue()) {
			res = thenExpr.accept(this);
		} else if (testValue.isFalse()) {
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
	public EvaluatableValue visit(FunctionCallExpr e) {
		List<EvaluatableValue> args = new ArrayList<>();
		EvaluatableArgList sig = new EvaluatableArgList();
		List<NamedType> argtypes = ftable.getArgTypes(e.function);
		int index = 0;
		for (Expr v: e.args) {
			PolyEvaluatableValue ev = (PolyEvaluatableValue) v.accept(this);
			args.add(ev);
			sig.add(Rat.ValueFromTypedFraction(argtypes.get(index), ev.cex()));
			index++;
		}
		String fn = e.function;
		// From the function name and the arguments we can get
		// the poly args and the poly return value.
		List<PolyEvaluatableValue> ufargs = ftable.getArgValues(fn,sig);
		PolyEvaluatableValue ufvalue = ftable.getFnValue(fn, sig);
		index = 0;
		for (EvaluatableValue v: args) {
			BooleanPoly res = (BooleanPoly) v.equalop(ufargs.get(index));
			if (Debug.isEnabled()) System.out.println(ID.location() + "Adding " + e.function + " Instance Constraint");
			GlobalState.addConstraint(res.value);
			index++;
		}
		if (Debug.isEnabled()) System.out.println(ID.location() + e + " evaluated to " + ufvalue + " [" + ufvalue.cex() + "]");
		return ufvalue;
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
