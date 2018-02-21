/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.poly;

import java.math.BigDecimal;
import java.math.BigInteger;

import fuzzm.lustre.SignalName;
import fuzzm.util.ID;
import fuzzm.util.OrderedObject;
import fuzzm.util.TypedName;
import fuzzm.value.poly.GlobalState;
import jkind.lustre.BinaryExpr;
import jkind.lustre.BinaryOp;
import jkind.lustre.BoolExpr;
import jkind.lustre.Expr;
import jkind.lustre.IntExpr;
import jkind.lustre.NamedType;
import jkind.lustre.RealExpr;
import jkind.util.BigFraction;

public class VariableID extends OrderedObject implements Comparable<VariableID> {

    public final SignalName name;
	public BigFraction cex;
	public final VariableRole role;

	private VariableID(String name, VariableRole vrole, NamedType type, BigFraction cex) {
		super();
		name = "|" + name + "_#" + count + "|";
		this.name = new SignalName(new TypedName(name,type),-1);
		this.cex = cex;
		this.role = vrole;
	}
	
	private VariableID(SignalName nameIn, VariableRole vrole, BigFraction cex){
		super();
		assert(Thread.holdsLock(GlobalState.class));
		this.name = nameIn;
		this.cex = cex;
		this.role = vrole;
	}
	
	private VariableID(SignalName nameIn, VariableRole vroll){
		this(nameIn,vroll,BigFraction.ZERO);
	}
	
	private VariableID(String nameIn, VariableRole vroll, NamedType type) {
		this(new SignalName(new TypedName(nameIn,type),0),vroll,BigFraction.ZERO);
	}
	

	public BigFraction getCex() {
		assert(wellOrdered());		
		assert(cex != null);
		return cex;
	}

	public void setCex(BigFraction cex) {
		this.cex = cex;
	}

	public Expr cexExpr() {
	    return (name.name.type == NamedType.BOOL) ? new BoolExpr(cex.signum() != 0) :
	           (name.name.type == NamedType.INT)  ? new IntExpr(cex.getNumerator()) :
	           new BinaryExpr(new RealExpr(new BigDecimal(cex.getNumerator())),BinaryOp.DIVIDE, 
	                          new RealExpr(new BigDecimal(cex.getDenominator())));
	}
	
	private static VariableID last = null;
	public static VariableID postAlloc(String base, NamedType type, BigFraction cex) {
		//System.out.println(ID.location(2) + "postAlloc()");
		VariableID res = new VariableID(base,VariableRole.AUXILIARY,type,cex);
		if (first == null) {
			first = res;
		}		
		res.insertAfter(last);
		last = res;
		assert(first.wellOrdered());
		assert(last != null && first != null && last.next == null);
		return res;
	}
	
	public VariableID afterAlloc(String base, NamedType type, BigFraction cex) {
		//System.out.println(ID.location(2) + "afterAlloc(" + this + ":" + this.level() + ")");
		VariableID res = new VariableID(base,VariableRole.AUXILIARY,type,cex);
		res.insertAfter(this);
		if (last.equals(this)) {
			last = res;
		}
		assert(first.wellOrdered());
		if (! (last != null && first != null && last.next == null)) {
			assert(false);
		}
		return res;		
	}
	
	private static VariableID first = null;
	public static VariableID principleAlloc(String base, NamedType type, BigFraction cex) {
		//System.out.println(ID.location(2) + "preAlloc()");
		VariableID res = new VariableID(base,VariableRole.PRINCIPLE,type,cex);
		if (last == null) {
			last = res;
		}
		first = (VariableID) res.insertBefore(first);
		assert(first.wellOrdered());
		assert(last != null && first != null && last.next == null);
		return res;
	}
	
	public static VariableID principleAlloc(SignalName nameIn, BigFraction cex) {
		//System.out.println(ID.location(2) + "preAlloc()");
		VariableID res = new VariableID(nameIn,VariableRole.PRINCIPLE,cex);
		if (last == null) {
			last = res;
		}
		first = (VariableID) res.insertBefore(first);
		assert(first.wellOrdered());
		assert(last != null && first != null && last.next == null);
		return res;		
	}
	
	@Override
	public int compareTo(VariableID arg0) {
		return (id() == arg0.id()) ? 0 : ((level() < arg0.level()) ? -1 : 1);
	}
	
	@Override
	public String toString() {
		return name.toString(); 
	}

    public String toACL2() {
        return "(id " + name.toString() + " " + ((name.name.type == NamedType.BOOL) ? ((cex.signum() == 0) ? "nil" : "t") : cex.toString()) + ")";
    }

    public String toACL2(String cex) {
        return "(id " + name.toString() + " " + cex + ")";
    }

	public static void clearGlobalState() {
		count = 0;
		last = null;
		first = null;
	}
}
