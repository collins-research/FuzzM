/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.poly;

import java.util.Map;
import java.util.Set;

import jkind.util.BigFraction;

public class VariableBoolean extends Variable {

	// We support a limited form of boolean generalization.
	// If the boolean variable appears in the final generalization,
	// is is restricted.  Otherwise it is unrestricted.  This is
	// important from a test generation standpoint: if the variable
	// isn't bound, it is free.
    
    // We always create the variable "true"
    // Later on we may negate it.
    // 
    
    // If the vid is bound to false, the variable must be negated.
    TargetType target;
    
    private static boolean isTrue(BigFraction f) {
        return (f.compareTo(BigFraction.ZERO) == 0) ? false : true;
    }
    
    public boolean isNegated() {
        return cex != isTrue(vid.cex);
    }
    
    private VariableBoolean(VariableID vid, boolean cex, TargetType target) {
		super(vid,cex);
		this.target = target;
	}

    public VariableBoolean(VariableID vid) {
        this(vid, true, TargetType.CHAFF);
    }

    public VariableBoolean(VariableBoolean src, TargetType target) {
        this(src.vid,src.cex,target);
    }
    
	@Override
	public RestrictionResult andTrue(Variable right) {
		return ((VariableInterface) right).andTrue2(this);
	}

	@Override
	public RestrictionResult andTrue2(VariableEquality left) {
		// TODO Auto-generated method stub
		throw new IllegalArgumentException();
	}

	@Override
	public RestrictionResult andTrue2(VariableInterval left) {
		// TODO Auto-generated method stub
		throw new IllegalArgumentException();
	}

	@Override
	public RestrictionResult andTrue2(VariableLess left) {
		// TODO Auto-generated method stub
		throw new IllegalArgumentException();
	}

	@Override
	public RestrictionResult andTrue2(VariableGreater left) {
		// TODO Auto-generated method stub
		throw new IllegalArgumentException();
	}

	@Override
	public RestrictionResult andTrue2(VariableBoolean left) {
		assert(this.cex == left.cex);
		assert(this.vid == left.vid);
		return new RestrictionResult(this);
	}

    @Override
    public String toACL2() {
        return toACL2(isTrue(vid.cex) ? "t" : "nil");
    }
    
    @Override
    public String toACL2(String cex) {
        // So .. the actual cex value is encoded in the negation.
        String name = vid.toACL2(cex);
        return isNegated() ? "(not " + name + ")" : name;
    }
    
    @Override
    public String toString() {
        String name = vid.toString();
        return isNegated() ? "(! " + target.toString() + name + ")" : (target.toString() + name);
    }

	@Override
	public int countFeatures() {
		return 1;
	}

	@Override
	public boolean isArtifact() {
	    return false;
	}
	
	@Override
	public boolean requiresRestriction() {
		return false;
	}

	@Override
	public RestrictionResult restriction() {
		// TODO Auto-generated method stub
		throw new IllegalArgumentException();
	}

	@Override
	public boolean reducableIntegerInterval() {
		return false;
	}

	@Override
	public RestrictionResult reducedInterval() {
		throw new IllegalArgumentException();
	}

	@Override
	protected RegionBounds constraintBounds(Map<VariableID, BigFraction> ctx) {
		return new RegionBounds(vid.cex);
	}

	@Override
    protected RegionBounds constraintBounds() {
        return new RegionBounds(vid.cex);
    }

	@Override
	protected RegionBounds intervalBounds(Map<VariableID,RegionBounds> ctx) {
		return new RegionBounds(vid.cex);
	}
	
	@Override
	public boolean implicitEquality() {
		return false;
	}

	@Override
	public Variable toEquality() {
		throw new IllegalArgumentException();
	}

	@Override
	public Set<VariableID> updateVariableSet(Set<VariableID> in) {
		return in;
	}

	@Override
	public boolean slackIntegerBounds() {
		return false;
	}

	@Override
	public Variable tightenIntegerBounds() {
		throw new IllegalArgumentException();
	}

	@Override
	public boolean evalCEX(Map<VariableID, BigFraction> ctx) {
		return isNegated() ^ isTrue(ctx.get(this.vid));
	}

	@Override
	public String cexString() {
		// TODO Auto-generated method stub
		throw new IllegalArgumentException();
	}

	@Override
	public Variable rewrite(Map<VariableID, AbstractPoly> rewrite) {
		return this;
	}

	@Override
	public AbstractPoly maxBound(int sign) {
		// TODO Auto-generated method stub
		throw new IllegalArgumentException();
	}

	@Override
	public BigFraction maxValue(int sign, Map<VariableID, BigFraction> ctx) {
		// TODO Auto-generated method stub
		throw new IllegalArgumentException();
	}

    @Override
    public RestrictionResult mustContain(AbstractPoly v) {
        // TODO Auto-generated method stub
        throw new IllegalArgumentException();
    }

    @Override
    public Variable target(boolean trueL, Variable right) {
        // !right => (!trueL ^ this)  when trueL = false
        return new VariableBoolean(this,(trueL == false) ? TargetType.TARGET : this.target);
    }

    @Override
    public Variable target2(boolean trueL, VariableEquality left) {
        throw new IllegalArgumentException();
    }

    @Override
    public Variable target2(boolean trueL, VariableInterval left) {
        throw new IllegalArgumentException();
    }

    @Override
    public Variable target2(boolean trueL, VariableLess left) {
        throw new IllegalArgumentException();
    }

    @Override
    public Variable target2(boolean trueL, VariableGreater left) {
        throw new IllegalArgumentException();
    }

    @Override
    public Variable target2(boolean trueL, VariableBoolean left) {
        throw new IllegalArgumentException();
    }

    @Override
    public Variable minSet(Variable right) {
        return this;
    }

    @Override
    public Variable minSet2(VariableEquality left) {
        throw new IllegalArgumentException();
    }

    @Override
    public Variable minSet2(VariableInterval left) {
        throw new IllegalArgumentException();
    }

    @Override
    public Variable minSet2(VariableLess left) {
        throw new IllegalArgumentException();
    }

    @Override
    public Variable minSet2(VariableGreater left) {
        throw new IllegalArgumentException();
    }

    @Override
    public Variable minSet2(VariableBoolean left) {
        return this;
    }

    @Override
    public boolean isTarget() {
        return target == TargetType.TARGET;
    }

    @Override
    public Variable maxSet(Variable right) {
        return this;
    }

    @Override
    public Variable maxSet2(VariableEquality left) {
        throw new IllegalArgumentException();
    }

    @Override
    public Variable maxSet2(VariableInterval left) {
        throw new IllegalArgumentException();
    }

    @Override
    public Variable maxSet2(VariableLess left) {
        throw new IllegalArgumentException();
    }

    @Override
    public Variable maxSet2(VariableGreater left) {
        throw new IllegalArgumentException();
    }

    @Override
    public Variable maxSet2(VariableBoolean left) {
        return this;
    }

    @Override
    public RestrictionResult andTrue2(VariablePhantom left) {
        return new RestrictionResult(this);
    }

    @Override
    public Variable minSet2(VariablePhantom left) {
        return this;
    }

    @Override
    public Variable maxSet2(VariablePhantom left) {
        return this;
    }

    @Override
    public Variable target2(boolean trueL, VariablePhantom left) {
        return Variable.target(this, true, left.v, trueL);
    }

}
