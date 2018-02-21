/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.poly;

import fuzzm.lustre.SignalName;
import fuzzm.util.OrderedObject;
import fuzzm.util.TypedName;
import fuzzm.value.poly.GlobalState;
import jkind.lustre.NamedType;
import jkind.util.BigFraction;

public class VariableID extends OrderedObject implements Comparable<VariableID> {

	public final SignalName name;
	public BigFraction cex;
	public final VariableType type;

	private VariableID(String name, VariableType vtype, NamedType type, BigFraction cex) {
		super();
		name = "|" + name + "_#" + count + "|";
		this.name = new SignalName(new TypedName(name,type),-1);
		this.cex = cex;
		this.type = vtype;
	}
	
	private VariableID(SignalName nameIn, VariableType vtype, BigFraction cex){
		super();
		assert(Thread.holdsLock(GlobalState.class));
		this.name = nameIn;
		this.cex = cex;
		this.type = vtype;
	}
	
	private VariableID(SignalName nameIn, VariableType vtype){
		this(nameIn,vtype,BigFraction.ZERO);
	}
	
	private VariableID(String nameIn, VariableType vtype, NamedType type) {
		this(new SignalName(new TypedName(nameIn,type),0),vtype,BigFraction.ZERO);
	}
	

	public BigFraction getCex() {
		assert(wellOrdered());		
		assert(cex != null);
		return cex;
	}

	public void setCex(BigFraction cex) {
		this.cex = cex;
	}
	
	private static VariableID last = null;
	public static VariableID postAlloc(String base, NamedType type, BigFraction cex) {
		//System.out.println(ID.location(2) + "postAlloc()");
		VariableID res = new VariableID(base,VariableType.AUXILIARY,type,cex);
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
		VariableID res = new VariableID(base,VariableType.AUXILIARY,type,cex);
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
		VariableID res = new VariableID(base,VariableType.PRINCIPLE,type,cex);
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
		VariableID res = new VariableID(nameIn,VariableType.PRINCIPLE,cex);
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

	public static void clearGlobalState() {
		count = 0;
		last = null;
		first = null;
	}
}
