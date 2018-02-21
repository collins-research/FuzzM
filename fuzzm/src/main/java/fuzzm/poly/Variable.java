package jfuzz.poly;

import java.util.Map;
import java.util.Set;

import jfuzz.value.poly.GlobalState;
import jkind.util.BigFraction;

abstract public class Variable implements VariableInterface {

	public final VariableID vid;
	public final boolean cex;
	
	public Variable(VariableID vid, boolean cex) {
		this.vid = vid;
		this.cex = cex;
	}
	
	abstract public String toACL2();
	abstract public String cexString();

	protected String statusString() {
		return "(" + (cex ? "T" : "F") + ((countFeatures() > 0) ? "*" : "") + ")";
	}
	
	abstract public int countFeatures();
	
	abstract public Variable andFalse(Variable arg);
	abstract public RestrictionResult andTrue(Variable arg);
	
	abstract public Variable not();
	
	abstract public boolean implicitEquality();
	abstract public Variable toEquality();
	
	abstract public boolean requiresRestriction();
	abstract public RestrictionResult restriction();
	
	abstract public boolean slackIntegerBounds();
	abstract public Variable tightenIntegerBounds();

	abstract public boolean  reducableIntegerInterval();
	abstract public RestrictionResult reducedInterval();
	
	abstract protected RegionBounds constraintBounds(Map<VariableID,BigFraction> ctx);
	abstract protected RegionBounds constraintBounds();
    abstract protected RegionBounds intervalBounds(Map<VariableID,RegionBounds> ctx);

	
	// ACL2: (def::un better (x y)
	static Variable better(Variable c1, Variable c2) {
		if (c1.countFeatures() > c2.countFeatures()) return c1;
		if (c2.countFeatures() > c1.countFeatures()) return c2;
		if (GlobalState.oracle().nextBoolean()) {
			return c1;
		} else {
			return c2;
		}
	}	

	static Variable secondOnlyIfBetter(Variable c1, Variable c2) {
		if (c2.countFeatures() > c1.countFeatures()) return c2;
		return c1;
	}

	abstract public Set<VariableID> updateVariableSet(Set<VariableID> in);

	abstract public boolean evalCEX(Map<VariableID, BigFraction> ctx);

	abstract public Variable rewrite(Map<VariableID, AbstractPoly> rewrite);

	abstract public AbstractPoly maxBound(int sign);

	abstract public BigFraction maxValue(int sign, Map<VariableID,BigFraction> ctx);

    abstract public RestrictionResult mustContain(AbstractPoly v);

}
