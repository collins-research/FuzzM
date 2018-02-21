package jfuzz.lustre;

import java.math.BigDecimal;

import jfuzz.util.RatSignal;
import jfuzz.util.Signal;
import jkind.lustre.BinaryExpr;
import jkind.lustre.BinaryOp;
import jkind.lustre.IdExpr;
import jkind.lustre.NamedType;
import jkind.lustre.RealExpr;
import jkind.lustre.UnaryExpr;
import jkind.lustre.UnaryOp;
import jkind.util.BigFraction;

public class ExprSignal extends Signal<ExprVect> {
	
	private static final long serialVersionUID = -7854773286758238743L;

	public ExprSignal() {
		super();
	}
	
	public ExprSignal(RatSignal s) {
		super();
		for (int time=0;time<s.size();time++) {
			add(new ExprVect(s.get(time)));
		}
	}
	
	public ExprSignal(int size, ExprVect v) {
		super();
		for (int time=0;time<size;time++) {
			add(v);
		}
	}
	
	public ExprCtx dot(ExprSignal x, String dotName) {
		// dot = (if (t=0) a*x .. 0) + (0 -> (pre dot))
		int size = Math.min(x.size(),size());
		SignalCtx signalCtx = new SignalCtx(NamedType.REAL);
		for (int time=0; time<size;time++) {
			signalCtx.add(get(time).dot(x.get(time)).bind(dotName + "_" + time + "_"));
		}
		RealExpr zero = new RealExpr(BigDecimal.ZERO);
		signalCtx.add(zero);
		ExprCtx dotExpr = signalCtx.bind(dotName + "_");
		dotExpr.op(BinaryOp.PLUS,new BinaryExpr(zero,BinaryOp.ARROW,new UnaryExpr(UnaryOp.PRE,new IdExpr(dotName))));
		dotExpr = dotExpr.bind(dotName);
		return dotExpr;
	}

	public ExprCtx dot(RatSignal x, String dotName) {
		return dot(new ExprSignal(x),dotName);
	}
	
	public ExprSignal mul(BigFraction M) {
		ExprSignal res = new ExprSignal();
		for (ExprVect v: this) {
			res.add(v.mul(M));
		}
		return res;
	}

	public ExprSignal add(ExprSignal x) {
		ExprSignal res = new ExprSignal();
		int size = Math.max(size(),x.size());
		for (int i=0;i<size;i++) {
			res.add(get(i).add(x.get(i)));
		}
		return res;
	}
	
	public ExprSignal add(RatSignal x) {
		return add(new ExprSignal(x));
	}
	
	public ExprSignal sub(ExprSignal x) {
		ExprSignal res = new ExprSignal();
		int size = Math.max(size(),x.size());
		for (int i=0;i<size;i++) {
			res.add(get(i).sub(x.get(i)));
		}
		return res;
	}

	public ExprSignal sub(RatSignal x) {
		return sub(new ExprSignal(x));
	}
	
	@Override
	public ExprVect get(int time) {
		if (time < size()) {
			return super.get(time);
		}
		return new ExprVect();
	}
	
	@Override
	public ExprVect set(int time, ExprVect value) {
		if (time < size()) {
			return super.set(time,value);
		}
		for (int i=size();i<time;i++) {
			add(new ExprVect());
		}
		add(value);
		return value;
	}

}
