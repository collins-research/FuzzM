package jfuzz.util;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * PartialOrder maintain a partial order within a set of initial
 * elements given a sequence of orderings specified (via update())
 * in the form (node > {body})
 * 
 * The associated iterator will iterate from smallest to largest.
 *
 * @param <T>
 */
public class PartialOrder<T> implements Iterable<T> {

	class Node {
		int level;
		Set<T> edges;
		public Node() {
			level = -1;
			edges = new HashSet<T>();
		}
		public Node(Collection<T> set) {
			level = -1;
			edges = new HashSet<T>(set);
		}
		void add(T element) {
			edges.add(element);
		}
		void addAll(Collection<T> elements) {
			edges.addAll(elements);
		}
		public String toString() {
			String res = "Node(" + level + ",{";
			String delimit = "";
			for (T e: edges) {
				res += delimit + e.toString();
				delimit = ",";
			}			
			return res + "})";
		}
	}
	
	private Map<T,Node> graph;
	private List<T> elements;
	private Set<T>  unbound;
	
	public PartialOrder() {
		graph = new HashMap<T,Node>();
		elements = null;
		unbound = new HashSet<>();
	}

	public PartialOrder(Map<T,Collection<T>> ingraph) {
		this();
		for (T key: ingraph.keySet()) {
			graph.put(key,new Node(ingraph.get(key)));
		}
	}

	public Map<T,Set<T>> getGraph() {
		Map<T,Set<T>> res = new HashMap<>();
		for (T key: graph.keySet()) {
			res.put(key,graph.get(key).edges);
		}
		return res;
	}
	
	private int orderNodes (int level, Collection<T> keys) {
		int res = level;
		for (T key: keys) {
			Node entry = graph.get(key);
			if (entry == null) {
				// Leaf nodes (no children)
				entry = new Node();
				graph.put(key,entry);
			}			
			if (entry.level < level) {
				entry.level = level;
				res = Math.max(res,orderNodes(level+1,entry.edges));
			}
		}
		return res;
	}
	
	private int orderNodes() {
		return orderNodes(0,new ArrayList<>(graph.keySet()));
	}

	private void resetOrder() {
		if (elements == null) return;
		elements = null;
		for (T key: graph.keySet()) {
			graph.get(key).level = -1;
		}
	}

	private void computeOrder() {
		int size = orderNodes();
		@SuppressWarnings("unchecked")
		Set<T> level[] = new HashSet[size];
		for (int index = 0; index<size; index++) {
			level[index] = new HashSet<>();
		}
		Set<T> keySet = graph.keySet();
		for (T key: keySet) {
			level[graph.get(key).level].add(key);
		}
		elements = new ArrayList<>();
		unbound.addAll(level[0]);
		for (int index = 1; index<size; index++) {
			elements.addAll(level[index]);
		}
		unbound.removeAll(elements);
		elements.addAll(0,unbound);
		//System.out.println("Processed Graph : " + graph);
	}
	
	public List<T> unbound() {
		if (elements == null) {
			computeOrder();
		}
		return new ArrayList<>(unbound);
	}
	
	public List<T> totalOrder() {
		if (elements == null) {
			computeOrder();
		}
		return elements;
	}
	
	public List<T> ordinalToEntry() {
		return totalOrder();
	}
	
	public Map<T,Integer> entryToOrdinal() {
		List<T> order = totalOrder();
		Map<T,Integer> res = new HashMap<T,Integer>();
		int index = 0;
		for (T entry: order) {
			res.put(entry,index);
			index++;
		}
		return res;
	}
	
	public void update(T node, Collection<T> body) {
		resetOrder();
		Node entry = graph.get(node);
		entry = (entry == null) ? new Node() : entry;
		entry.addAll(body);
		graph.put(node, entry);
	}
	
	public void update(Collection<T> nodes, Collection<T> body) {
		if (nodes.isEmpty()) unbound.addAll(body);
		for (T node: nodes) {
			update(node,body);
		}
	}
	
	public void update(T node, T body) {
		Set<T> entry = new HashSet<T>();
		entry.add(body);
		update(node,entry);
	}
	
	public void update(Collection<T> nodes, T body) {
		if (nodes.isEmpty()) unbound.add(body);
		for (T node: nodes) {
			update(node,body);
		}
	}

	public void update(T node) {
		resetOrder();
		Node entry = graph.get(node);
		entry = (entry == null) ? new Node() : entry;
		graph.put(node, entry);
	}

	@Override
	public Iterator<T> iterator() {
		List<T> res = new ArrayList<T>(totalOrder());
		Collections.reverse(res);
		return res.iterator();
	}
	
	public static void main(String args[]) {
		PartialOrder<String> order = new PartialOrder<>();
		order.update("A","B");
		order.update("A","C");
		order.update("A","D");
		List<String> Torder = order.totalOrder();
		String delimitor = "";
		for (String name: Torder) {
			System.out.print(delimitor + name);
			delimitor = " ";
		}
		System.out.println("");
		order.update("D","C");
		Torder = order.totalOrder();
		delimitor = "";
		for (String name: Torder) {
			System.out.print(delimitor + name);
			delimitor = " ";
		}
		System.out.println("");
		order.update("C","B");
		Torder = order.totalOrder();
		delimitor = "";
		for (String name: Torder) {
			System.out.print(delimitor + name);
			delimitor = " ";
		}
		System.out.println("");
		order = new PartialOrder<>();
		order.update("A","B");
		order.update("A","C");
		Torder = order.totalOrder();
		delimitor = "";
		for (String name: Torder) {
			System.out.print(delimitor + name);
			delimitor = " ";
		}
		System.out.println("");
	}
	
}
