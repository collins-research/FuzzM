package jfuzz.util;

import jfuzz.poly.VariableID;

public class OrderedObject {

	protected OrderedObject next;
	private int level;
	private final int id;
	protected static int count = 0;
	
	protected OrderedObject() {
		this.next = null;
		this.level = 0;
		this.id = count;
		count++;
	}
	
	public int level() {
		return level;
	}
	
	public int id() {
		return id;
	}
	
	public OrderedObject insertBefore(OrderedObject arg) {
		if (arg == null) {
			this.next = null;
			this.level = 0;
		} else {
			this.next = arg;
			this.level = arg.level+1;
		}
		return this;
	}

	public void insertAfter(OrderedObject arg) {
		//System.out.println(ID.location() + "Inserting " + this + " after " + arg);
		if (arg == null) {
			this.next = null;
			this.level = 0;
		} else {
			OrderedObject old_next = arg.next;
			arg.next = this;
			this.next = old_next;
			this.renumber(arg.level-1);
		}
	}
	
	private void renumber(int nextLevel) {
		//System.out.println(ID.location() + "Renumbering ..");
		OrderedObject curr = this;
		while (curr != null) {
			//System.out.println(ID.location() + curr + " from " + curr.level + " to " + nextLevel);
			curr.level = nextLevel;
			nextLevel--;
			curr = curr.next;
		}
	}
	
	protected  boolean wellOrdered() {
		OrderedObject curr = this;
		while (curr.next != null) {
			assert(curr.level() == curr.next.level() + 1);
			curr = curr.next;
		}
		return true;
	}
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		//result = prime * result + ((name == null) ? 0 : name.hashCode());
		result = prime * result + id;
		return result;
	}
	
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (! (obj instanceof VariableID))
			return false;
		VariableID other = (VariableID) obj;
		if (id != other.id())
			return false;
		return true;
	}

}
