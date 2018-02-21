package jfuzz.lustre.generalize;

import jfuzz.lustre.evaluation.PolyFunctionMap;
import jfuzz.poly.PolyBool;

public class PolyGeneralizationResult {
	public PolyBool result;
	public PolyFunctionMap fmap;
	public PolyGeneralizationResult(PolyBool res, PolyFunctionMap fmap) {
		this.result = res;
		this.fmap = fmap;
	}
}
