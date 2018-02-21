package jfuzz.lustre.evaluation;

import jfuzz.value.hierarchy.EvaluatableValue;
import jkind.lustre.BinaryExpr;
import jkind.lustre.BinaryOp;
import jkind.lustre.BoolExpr;
import jkind.lustre.FunctionCallExpr;
import jkind.lustre.IdExpr;
import jkind.lustre.IntExpr;
import jkind.lustre.RealExpr;
import jkind.lustre.UnaryExpr;
import jkind.lustre.UnaryOp;
import jkind.lustre.values.Value;

public class InitEvaluatableValueEvaluator extends BaseEvaluatableValueEvaluator {

	BaseEvaluatableValueEvaluator evaluator;
	
	public InitEvaluatableValueEvaluator(BaseEvaluatableValueEvaluator evaluator) {
		super(evaluator.fns);
		this.evaluator = evaluator;
	}
	
	@Override
	public Value visit(BinaryExpr e) {
		if (e.op.equals(BinaryOp.ARROW)) {
			return e.left.accept(this);
		}
		return super.visit(e);
	}

	@Override
	public Value visit(UnaryExpr e) {
		if (e.op.equals(UnaryOp.PRE)) {
			assert(false);
		}
		return super.visit(e);
	}

	@Override
	public Value visit(IdExpr e) {
		return evaluator.visit(e);
	}

	@Override
	public EvaluatableValue visit(IntExpr e) {
		return evaluator.visit(e);
	}

	@Override
	public EvaluatableValue visit(RealExpr e) {
		return evaluator.visit(e);
	}

	@Override
	public EvaluatableValue visit(BoolExpr e) {
		return evaluator.visit(e);
	}

	@Override
	public EvaluatableValue visit(FunctionCallExpr e) {
		return evaluator.visit(e);
	}

}
