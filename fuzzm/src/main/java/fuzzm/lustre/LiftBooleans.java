package jfuzz.lustre;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import jfuzz.util.PartialOrder;
import jkind.lustre.Equation;
import jkind.lustre.IdExpr;
import jkind.lustre.NamedType;
import jkind.lustre.Node;
import jkind.lustre.NodeCallExpr;
import jkind.lustre.Program;
import jkind.lustre.VarDecl;
import jkind.lustre.builders.NodeBuilder;
import jkind.lustre.builders.ProgramBuilder;

public class LiftBooleans {

	Map<String,List<String>> newNodeOutputs;
	List<String> newOutputs;
	int count;
	
	private LiftBooleans(Map<String,List<String>> newNodeOutputs) {
		this.newNodeOutputs = newNodeOutputs;
		this.newOutputs = null;
		this.count = 0;
	}
	
	public static Program lift(Program program) {
		PartialOrder<String> order = OrderNodes.computeOrder(program);
		ProgramBuilder pb = new ProgramBuilder(program);
		LiftBooleans res = new LiftBooleans(new HashMap<String,List<String>>());
		Map<String,Node> nmap = new HashMap<String,Node>();
		for (Node n: program.nodes) {
			nmap.put(n.id,n);
		}
		for (String nodeName: order) {
			Node n = nmap.get(nodeName);
			n = res.updateNode(n);
			nmap.put(nodeName, n);
		}
		pb.clearNodes();
		pb.addNodes(nmap.values());
		return pb.build();
	}
	
	private Node updateNode(Node e) {
		NodeBuilder nb = new NodeBuilder(e);	
		// Transfer all boolean locals to output
		newOutputs = new ArrayList<String>();
		count = 0;
		nb.clearLocals();
		for (VarDecl vd: e.locals) {
			if (vd.type == NamedType.BOOL) {
				newOutputs.add(vd.id);
			} else {
				nb.addLocal(vd);
			}
		}
		nb.clearEquations();
		for (Equation eq: e.equations) {
			// Update all of the equations and 
			// collect all of the new outputs
			nb.addEquation(updateEquation(eq));
		}
		
		List<VarDecl> outDecls = new ArrayList<VarDecl>();
		for (String s: newOutputs) {
			outDecls.add(new VarDecl(s,NamedType.BOOL));
		}
		nb.addOutputs(outDecls);
		newNodeOutputs.put(e.id, newOutputs);
		return nb.build();
	}

	private Equation updateEquation(Equation e) {
		if (e.expr instanceof NodeCallExpr) {
			NodeCallExpr call = (NodeCallExpr) e.expr;
			List<IdExpr> lhs = new ArrayList<IdExpr>(e.lhs);
			assert(newNodeOutputs.containsKey(call.node));
			for (String s: newNodeOutputs.get(call.node)) {
				String newID = "_" + call.node + count + "_" + s;
				newOutputs.add(newID);
				lhs.add(new IdExpr(newID));
			}
			count++;
			e = new Equation(e.location,lhs,e.expr);
		}
		return e;
	}
	
	
}

