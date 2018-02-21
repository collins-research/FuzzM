/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.lustre.evaluation;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;
import java.util.stream.Collectors;

import fuzzm.lustre.SignalName;
import fuzzm.lustre.StepDependency;
import fuzzm.lustre.indexed.IndexIdentifiers;
import fuzzm.util.EvaluatableSignal;
import fuzzm.util.PartialOrder;
import fuzzm.util.TypedName;
import fuzzm.value.bound.BoundValue;
import fuzzm.value.hierarchy.EvaluatableValue;
import jkind.lustre.Equation;
import jkind.lustre.Expr;
import jkind.lustre.IntExpr;
import jkind.lustre.NamedType;
import jkind.lustre.Node;
import jkind.lustre.Program;
import jkind.lustre.Type;
import jkind.lustre.VarDecl;

public abstract class EventBasedSimulator extends IndexedEvaluator {
	
	class ExtendedHashMap<T> extends HashMap<T,Set<T>> {
		private static final long serialVersionUID = -7814687305325701160L;
		public void update(T key, T value) {
			Set<T> values = get(key);
			values = (values == null) ? new HashSet<T>() : values;
			values.add(value);
			put(key,values);
		}
		public void updateAll(Collection<T> keys, T value) {
			for (T key: keys) {
				update(key,value);
			}
		}
	}
	
	protected final Node main;
	protected final List<String> indexToName;
	protected final Map<String,Integer> nameToIndex;
	protected final BoundValue binding[][];
	protected Expr equation[];
	//protected final String property;
	protected final int k;
	
	public EventBasedSimulator(EvaluatableSignal inputs, FunctionLookupEV fns, String property, Program model, SimulationResults res) {
		super(fns);
		
		Node specNode = model.getMainNode();
		k = inputs.size();
		//this.property = property;

		Map<String,Type> typeMap = new HashMap<>();
		for (VarDecl vd: specNode.inputs) {
			typeMap.put(vd.id, vd.type);
		}
		for (VarDecl vd: specNode.outputs) {
			typeMap.put(vd.id, vd.type);
		}
		for (VarDecl vd: specNode.locals) {
			typeMap.put(vd.id, vd.type);
		}
		
		PartialOrder<String> order = new PartialOrder<>();
		Collection<String> empty = new ArrayList<String>();
		for (VarDecl vd: specNode.inputs) {
			order.update(vd.id,empty);
		}
		ExtendedHashMap<String> nextSGraph = new ExtendedHashMap<>();
		for (Equation eq: specNode.equations) {
			//System.out.println("Equation : " + eq);
			StepDependency deps = StepDependency.computeDependencies(eq.expr);
			Set<String> preSet = deps.getPreSet();
			Set<String> depSet = deps.getDepSet();
			//StringJoiner joiner1 = new StringJoiner(",","","");
			//preSet.forEach(joiner1::add);
			//System.out.println("preSet : {" + joiner1 + "}");
			//StringJoiner joiner2 = new StringJoiner(",","","");
			//depSet.forEach(joiner2::add);
			//System.out.println("depSet : {" + joiner2 + "}");
			assert(eq.lhs.size() == 1);
			String id = eq.lhs.get(0).id;
			order.update(depSet,id);
			nextSGraph.updateAll(preSet,id);
		}
		// Assertions must all be true.  Assertions will
		// be identified as numbers in the form of strings.
		List<String> inputNames = specNode.inputs.stream().map(x -> x.id).collect(Collectors.toList());
		Integer assertionID = 0;
		List<String> assertionIDs = new ArrayList<>();
		for (Expr ex: specNode.assertions) {
			//System.out.println(ID.location() + "Assertion " + assertionID + " : " + ex);
			StepDependency deps = StepDependency.computeDependencies(ex);
			Set<String> preSet = deps.getPreSet();
			Set<String> depSet = deps.getDepSet();
			String assertionName = assertionID.toString();
			assertionIDs.add(assertionName);
			order.update(depSet,assertionName);
			nextSGraph.updateAll(preSet,assertionName);
			assertionID += 1;
		}

		// There is an interaction between the total order and the scheduling of events.
		// The events are processed from lowest to highest.  Thus, we may attempt to
		// schedule an event with a high total order even before all of its predecessors
		// have been processed.  However, it will not be evaluated until after those
		// predecessors because they have a lower total order.
		indexToName = order.totalOrder();
		//System.out.println(ID.location() + "indexToName : " + indexToName);

		List<String> unboundNames = order.unbound();
		//System.out.println(ID.location() + "unboundNames : " + unboundNames);
		
		int totalBindings = indexToName.size();

		// Construct a mapping from names to indices.
		nameToIndex = new HashMap<>();
		for (int index = 0; index<indexToName.size(); index++) {
			nameToIndex.put(indexToName.get(index),index);
		}
		assert(nameToIndex.containsKey(property));
		
		// Index all of the identifiers in the model.
		main = IndexIdentifiers.indexIdentifiers(specNode,nameToIndex);
		
		Map<String,Set<String>> currSGraph = order.getGraph();
		
		@SuppressWarnings("unchecked")
		SortedSet<Integer> currIGraph[] = new SortedSet[indexToName.size()];
		@SuppressWarnings("unchecked")
		SortedSet<Integer> nextIGraph[] = new SortedSet[indexToName.size()];
		
		for (String key: currSGraph.keySet()) {
			Collection<String> sset = currSGraph.get(key);
			TreeSet<Integer> iset = new TreeSet<>();
			for (String s: sset) {
				iset.add(nameToIndex.get(s));
			}
			currIGraph[nameToIndex.get(key)] = iset;
		}
				
		for (String key: nextSGraph.keySet()) {
			Collection<String> sset = nextSGraph.get(key);
			TreeSet<Integer> iset = new TreeSet<>();
			for (String s: sset) {
				iset.add(nameToIndex.get(s));
			}
			nextIGraph[nameToIndex.get(key)] = iset;
		}
				
		// Initialize equations and Bound Values ..
		binding  = new BoundValue[k][totalBindings];
		equation = new Expr[totalBindings];
		
		for (String name: inputNames) {
			// Some inputs may not appear in one or more of the graphs above ..
			//System.out.println(ID.location() + "Name : " + name);
			//assert(nameToIndex.containsKey(name));
			
			int index = nameToIndex.get(name);
			SortedSet<Integer> currSet = currIGraph[index];
			SortedSet<Integer> nextSet = nextIGraph[index];
			TypedName tname = new TypedName(name,(NamedType) typeMap.get(name));
			for (int time=0;time<k;time++) {
				binding[time][index] = inputValue(inputs.get(time).get(tname),typeMap.get(name),currSet,nextSet);
			}
			equation[index] = new IntExpr(0);
		}
		for (Equation e: main.equations) {
			String name = e.lhs.get(0).id;
			int index = nameToIndex.get(name);
			SortedSet<Integer> currSet = currIGraph[index];
			SortedSet<Integer> nextSet = nextIGraph[index];
			for (int time=0;time<k;time++) binding[time][index] = computedValue(typeMap.get(name),currSet,nextSet);
			equation[index] = e.expr;
		}
		assertionID = 0;
		for (Expr ex: main.assertions) {
			String assertionName = assertionID.toString();
			int index = nameToIndex.get(assertionName);
			for (int time=0;time<k;time++) binding[time][index] = constrainedValue(true);
			equation[index] = ex;
			assertionID += 1;
		}

		// Express the property as a constraint ..
		binding[k-1][nameToIndex.get(property)] = constrainedValue(false);
		
		@SuppressWarnings("unchecked")
		TreeSet<Integer> activeInputs[] = new TreeSet[k];
		TreeSet<Integer> inputSet = new TreeSet<>();
		for (String name: unboundNames) {
			inputSet.add(nameToIndex.get(name));
		}
		for (String name: inputNames) {
			inputSet.add(nameToIndex.get(name));
		}
		// System.out.println("Sorted Inputs :" + inputSet);
		for (int time=0;time<k;time++) {
			activeInputs[time] = inputSet;
		}
		SimulationResults satisfied = simulateSystem(activeInputs,res);
		// The property must be false in the final time step.
		assert(satisfied.isSatisfactory());
	}
	
	public BoundValue getBinding(String name, int time) { 
		return binding[time][nameToIndex.get(name)];
	}
	
	public SimulationResults simulateSystem(String name, int time, EvaluatableValue value, SimulationResults res) {
		int index = nameToIndex.get(name);
		binding[time][index].setValue(value);
		@SuppressWarnings("unchecked")
		TreeSet<Integer> activeInputs[] = new TreeSet[k];
		TreeSet<Integer> inputSet =  new TreeSet<>();
		inputSet.add(index);
		activeInputs[time] = inputSet;
		return simulateSystem(activeInputs,res);
	}
	
	public SimulationResults isConsistent(Map<SignalName,EvaluatableValue> newValues, SimulationResults res) {
		Map<SignalName,EvaluatableValue> oldValues = new HashMap<>();
		@SuppressWarnings("unchecked")
		TreeSet<Integer> activeInputs[] = new TreeSet[k];
		for (int time=0;time<k;time++) {
			activeInputs[time] = new TreeSet<>();
		}
		for (SignalName si: newValues.keySet()) {
			String name = si.name.name;
			int time = si.time;
			int index = nameToIndex.get(name);
			oldValues.put(si, getBinding(name,time).getValue());
			activeInputs[si.time].add(index);
			binding[time][index].setValue(newValues.get(si));	
		}
		SimulationResults consistencyResult = simulateSystem(activeInputs,res);
		if (! consistencyResult.isSatisfactory()) {
			for (SignalName si: oldValues.keySet()) {
				String name = si.name.name;
				int time = si.time;
				int index = nameToIndex.get(name);
				binding[time][index].setValue(oldValues.get(si));	
			}
			if (! simulateSystem(activeInputs,res).isSatisfactory()) assert(false);
		}
		return consistencyResult;
	}
	
	public SimulationResults isConsistent(SignalName si, EvaluatableValue value, SimulationResults res) {
		String name = si.name.name;
		int time = si.time;
		EvaluatableValue oldValue = getBinding(name,time).getValue();
		//System.out.println(ID.location());
		//System.out.println(ID.location() + "Checking : " + si + " = " + value);
		SimulationResults consistent = simulateSystem(name,time,value,res);
		if (! consistent.isSatisfactory()) {
			//System.out.println(ID.location());
			//System.out.println(ID.location() + "Retracting ..");
			//System.out.println(ID.location());
			simulateSystem(name,time,oldValue,res);
		} else {
			//System.out.println(ID.location() + "Consistent.");
		}
		return consistent;
	}
	
	public SimulationResults simulateSystem(TreeSet<Integer> inputs[], SimulationResults res) {
		// null input entries == empty sets.
		TreeSet<Integer> currQueue;
		TreeSet<Integer> nextQueue = new TreeSet<>();
		// So our simulation will take place starting from time 0 and incrementing forward.
		// We have two defSets .. one for the current time step and one for the next time step.
		// When we update our tick, we transfer the next to the current and clear the next.
		// Initial simulation ..
		// int spot = 0;
		//
		// TODO: Somehow this does not use the IndexedEvaluator class in any useful capacity.
		// Perhaps we should figure out why ??
		//System.out.println(ID.location() + "Initial Bindings : " + binding[0]);
		for (int time=0;time<k;time++) {
			currQueue = nextQueue;
			nextQueue = new TreeSet<>();
			if (inputs[time] != null) currQueue.addAll(inputs[time]);
			while (! currQueue.isEmpty()) {
				int index = currQueue.pollFirst();
				BoundValue x = binding[time][index];
				Expr ex = equation[index];
				//System.out.println("Binding Equation : " + indexToName.get(index) + "<" + index + "> = " + ex);
				//if (spot == 0) {
				// System.out.println(ID.location() + "Simulating : " + indexToName.get(index)); //  + " = " + x);
				//}
				//spot = (spot + 1) % 10000;
				int change = (time == 0) ? x.initValue(ex,binding[0]) : x.stepValue(ex,binding[time-1],binding[time]);
				//System.out.println(indexToName.get(index) + ((change != 0) ? " updated to " : " stayed at ") + x.getValue());
				if (change != 0) {
					if (change < 0) {
						//if (Debug.isEnabled()) System.out.println(ID.location() + "Simulation[" + time + "] " + indexToName.get(index) + " : Update");
						res = res.and(x.getValue());
						if (! res.isSatisfactory()) return res;
					} else {
						//System.out.println(ID.location() + "Simulation[" + time + "] " + indexToName.get(index) + " = " + x.getValue() + " *");
						currQueue.addAll(x.defSet);
						nextQueue.addAll(x.nextSet);
					}
				} else {
					//System.out.println(ID.location() + "Simulation[" + time + "] " + indexToName.get(index) + " = " + x.getValue());
				}
				//if (Debug.isEnabled()) System.out.println(ID.location() + "[" + time + "] " + indexToName.get(index) + " := (" + x.getValue() + ")");
			}
		}
		return res;
	}
	
}
