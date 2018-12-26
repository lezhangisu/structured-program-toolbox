package edu.iastate.structured.core;

import java.util.ArrayList;
import java.util.List;

import com.ensoftcorp.atlas.core.db.graph.Node;
import com.ensoftcorp.atlas.core.db.set.AtlasHashSet;
import com.ensoftcorp.atlas.core.db.set.AtlasSet;
import com.ensoftcorp.atlas.core.query.Q;
import com.ensoftcorp.atlas.core.xcsg.XCSG;
import com.ensoftcorp.atlas.java.core.script.Common;
import com.ensoftcorp.open.commons.algorithms.DominanceAnalysis;
import com.ensoftcorp.open.commons.algorithms.UniqueEntryExitControlFlowGraph;
import com.ensoftcorp.atlas.core.db.set.AtlasSet;
import com.ensoftcorp.atlas.core.db.graph.Graph;
import com.ensoftcorp.atlas.core.db.graph.Node;
import com.ensoftcorp.atlas.core.db.graph.Edge;

public class Structured {
	
	public static Graph test(Q cfg, Node node) {
		List<AtlasSet<Node>> l = getIfBlock(cfg, node);
		return Common.toQ(l.get(0)).union(Common.toQ(l.get(1))).union(Common.toQ(l.get(2))).induce(cfg).eval();

		
	}
	
	public static Graph test(Q cfg) {
//		return computeDominanceTree(cfg);
		Q cfbe=cfg.edges(XCSG.ControlFlowBackEdge).retainEdges(); //Control flow back edge
		Graph dag=cfg.differenceEdges(cfbe).retainEdges().eval();
//		return removeGotoEdge(cfg);
		return dag;
	}
	
	private static Graph removeGotoEdge(Q cfg) {
		Q cfbe=cfg.edges(XCSG.ControlFlowBackEdge).retainEdges(); //Control flow back edge
		Graph dag=cfg.differenceEdges(cfbe).retainEdges().eval(); // Control flow back edges removed
		Q dagQ = Common.toQ(dag);
		
		AtlasSet<Edge> edges = cfg.eval().edges();
		AtlasSet<Node> gotoNodes = cfg.nodes(XCSG.GotoStatement).eval().nodes();
		AtlasSet<Node> labelNodes = cfg.nodes("isLabel").eval().nodes();
		AtlasSet<Edge> gotoEdges = dagQ.between(Common.toQ(gotoNodes), Common.toQ(labelNodes)).retainEdges().eval().edges();
		return Common.toQ(edges).difference(Common.toQ(gotoEdges)).eval();
	}

	private static Graph computeDominanceTree(Q graphQ) {
		Graph graph = graphQ.eval();
		AtlasSet<Node> graphRoots = graphQ.roots().eval().nodes();
		AtlasSet<Node> graphLeaves = graphQ.leaves().eval().nodes();
		
		UniqueEntryExitControlFlowGraph uGraph = new UniqueEntryExitControlFlowGraph(graph, graphRoots, graphLeaves);
		Graph idomTree = DominanceAnalysis.computeDominanceTree(uGraph);
		
		AtlasSet<Node> comEntryExit = Common.toQ(idomTree).nodes("UniqueEntryExitCFG_Master_Entry","UniqueEntryExitCFG_Master_Exit").eval().nodes();
		
		Graph cleanIdomTree = Common.toQ(idomTree).difference(Common.toQ(comEntryExit)).induce(Common.toQ(idomTree)).eval();
		
		return cleanIdomTree;
	}
	
	private static List<AtlasSet<Node>> getIfBlock(Q cfg, Node node){
		Q cfbe=cfg.edges(XCSG.ControlFlowBackEdge).retainEdges(); //Control flow back edge
		Graph dag=cfg.differenceEdges(cfbe).retainEdges().eval(); // Control flow back edges removed
		Q dagQ = Common.toQ(dag);
		AtlasSet<Node> dagLeaves = dagQ.leaves().eval().nodes();
		
		// collect branch nodes
		AtlasSet<Node> branchNodes = cfg.successors(Common.toQ(node)).eval().nodes();
		
		// check if the false leave is a control flow back edge
		AtlasSet<Edge> cfbe_false_edge = cfg.forwardStep(Common.toQ(node)).selectEdge(XCSG.conditionValue, "false", false).retainEdges()
				.edgesTaggedWithAny(XCSG.ControlFlowBackEdge).eval().edges();
		
		if(cfbe_false_edge.size() > 0) {
			List<AtlasSet<Node>> return_list = new ArrayList<AtlasSet<Node>>();

			//entry
			return_list.add(Common.toQ(node).eval().nodes());
			//body untrimed
			return_list.add(dagQ.forward(Common.toQ(node)).difference(Common.toQ(node)).eval().nodes());
			//exit
			return_list.add(Common.toQ(cfbe_false_edge).leaves().eval().nodes());

			return return_list;
		}
		
		// collect the paths from each branch node to DAG leaves
		List<AtlasSet<Node>> listOfPaths = new ArrayList<AtlasSet<Node>>();
		for(Node branch_root : branchNodes) {
			listOfPaths.add(dagQ.between(Common.toQ(branch_root), Common.toQ(dagLeaves)).eval().nodes());
		}

		// For every two branch paths, find if there is an intersection
		// save the common intersection to this query
		AtlasSet<Node> intersectionNodeSet = new AtlasHashSet<Node>();

		for(int i = 0; i<listOfPaths.size()-1; i++) {
			for(int j = i+1; j<listOfPaths.size(); j++) {
				// get intersections of two branches
				AtlasSet<Node> tmp_joint_paths_node_set = Common.toQ(listOfPaths.get(i)).intersection(Common.toQ(listOfPaths.get(j))).eval().nodes();
				if(tmp_joint_paths_node_set.size()>0) {
					intersectionNodeSet.addAll(tmp_joint_paths_node_set);
				}
			}
		}
		Q intersection = Common.toQ(intersectionNodeSet);

		Graph subgraph = null;

		// get subgraph nodes
		if(intersectionNodeSet.size() == 0) {
			subgraph = dagQ.between(Common.toQ(branchNodes), Common.toQ(dagLeaves)).eval();
		}else {
			subgraph = dagQ.between(Common.toQ(branchNodes), Common.toQ(dagLeaves)).
					difference(intersection).union(intersection.induce(dagQ).roots()).eval();
		}
		
//		AtlasSet<Node> trueBranch = cfg.between(cfg.forwardStep(Common.toQ(node)).selectEdge(XCSG.conditionValue, "true", true)).eval().nodes();
//		AtlasSet<Node> falseBranch = cfg.forwardOn(cfg.forwardStep(Common.toQ(node)).selectEdge(XCSG.conditionValue, "false", false)).eval().nodes();
//		
//		AtlasSet<Node> intersection = Common.toQ(trueBranch).intersection(Common.toQ(falseBranch)).eval().nodes();
//		
//		Graph subgraph = null;
//		
//		// if it has intersection
//		if(intersection.size()>0) {
//			subgraph = dagQ.between(Common.toQ(node), Common.toQ(dagLeaves)).difference(Common.toQ(intersection)).union(Common.toQ(intersection).induce(dagQ).retainEdges().roots()).eval();
//		}
//		
//		return Common.toGraph(intersection);
		
		AtlasSet<Node> subgraph_entry = Common.toQ(node).eval().nodes();
		AtlasSet<Node> subgraph_exit = Common.toQ(subgraph).leaves().eval().nodes();
		AtlasSet<Node> subgraph_body = Common.toQ(subgraph).difference(Common.toQ(subgraph_entry)).difference(Common.toQ(subgraph_exit)).eval().nodes();
		
		List<AtlasSet<Node>> return_list = new ArrayList<AtlasSet<Node>>();
		
		return_list.add(subgraph_entry);
		return_list.add(subgraph_body);
		return_list.add(subgraph_exit);
		
		return return_list;
	}
	
	private static List<AtlasSet<Node>> getSwitchBlock(Q cfg, Node node){
		
		List<AtlasSet<Node>> return_list = new ArrayList<AtlasSet<Node>>();
		return return_list;
	}
	
	private static List<AtlasSet<Node>> getLoopBlock(Q cfg, Node node){
		Q cfbe=cfg.edges(XCSG.ControlFlowBackEdge).retainEdges(); //Control flow back edge
		Graph dag=cfg.differenceEdges(cfbe).retainEdges().eval(); // Control flow back edges removed
		Q dagQ = Common.toQ(dag);
		AtlasSet<Node> dagLeaves = dagQ.leaves().eval().nodes();
		
		AtlasSet<Edge> falseEdge = cfg.forwardStep(Common.toQ(node)).
				selectEdge(XCSG.conditionValue, "false", false).eval().edges(); // retainEdges to exclude isolated nodes

		// get false node
		Node falseNode = Common.toQ(falseEdge).leaves().eval().nodes().getFirst();
		
		// get label nodes
		AtlasSet<Node> labelNode = cfg.nodesTaggedWithAny("isLabel").eval().nodes();
		
		// label stopping node
		AtlasSet<Node> labelStopNode = Common.toQ(labelNode).difference(cfg.nodesTaggedWithAny(XCSG.Loop)).eval().nodes();

		// get the subgraph
		Graph subgraph =
				// get the part from loop condition to DAG leaves (to include the loop and return statements)
				dagQ.between(Common.toQ(node), Common.toQ(dagLeaves)).
				// get the part from loop condition to false node (to include possible break statements)
				union(dagQ.between(Common.toQ(node), Common.toQ(falseNode))).
				// exclude the part from false node to DAG leaves
				difference(dagQ.between(Common.toQ(falseNode), Common.toQ(dagLeaves)).retainEdges()).
				// exclude the part from label node to DAG leaves
				difference(dagQ.between(Common.toQ(labelStopNode), Common.toQ(dagLeaves)).retainEdges()).
				// put back false node and false edge to make the subgraph complete
				union(Common.toQ(falseNode)).union(Common.toQ(falseEdge)).union(Common.toQ(labelNode)).retainEdges().eval();

		// use induce(cfg) to add missing edges from CFG so we have complete subgraph
		subgraph = Common.toQ(subgraph).induce(cfg).retainEdges().eval();

		// get exit nodes
		AtlasSet<Node> subgraph_exit = Common.toQ(subgraph).leaves().eval().nodes();

		// get legal entry nodes
		AtlasSet<Node> subgraph_entry = Common.toQ(node).eval().nodes();

		// pick up other illegal entry nodes
		AtlasSet<Node> illegal_entry_set = new AtlasHashSet<Node>();

		for(Node n : Common.toQ(subgraph).difference(Common.toQ(subgraph_exit)).eval().nodes()) {
			for(Node ent : cfg.predecessors(Common.toQ(n)).eval().nodes()) {
				if(!Common.toQ(subgraph).eval().nodes().contains(ent)) {
					illegal_entry_set.add(n);
				}
			}
		}
		subgraph_entry = Common.toQ(subgraph_entry).union(Common.toQ(illegal_entry_set)).eval().nodes();
		
		AtlasSet<Node> subgraph_body = Common.toQ(subgraph).retainEdges().difference(Common.toQ(subgraph_entry)).difference(Common.toQ(subgraph_exit)).eval().nodes();
		
		List<AtlasSet<Node>> return_list = new ArrayList<AtlasSet<Node>>();

		return_list.add(subgraph_entry);
		return_list.add(subgraph_body);
		return_list.add(subgraph_exit);

		return return_list;
	}
	
	private static List<AtlasSet<Node>> getLabelModule(Q cfg, Node label){
		Q cfbe=cfg.edges(XCSG.ControlFlowBackEdge).retainEdges(); //Control flow back edge
		Graph dag=cfg.differenceEdges(cfbe).retainEdges().eval(); // Control flow back edges removed
		Q dagQ = Common.toQ(dag);
		
		Q break_nodes = cfg.nodes(XCSG.Break);
		Q break_edges = cfg.forwardStep(break_nodes).retainEdges();
		
		Graph dag_no_break = dagQ.differenceEdges(break_edges).retainEdges().eval();
		Q dag_no_breakQ = Common.toQ(dag_no_break);
		
		Q subgraphQ = dag_no_breakQ.forward(Common.toQ(label));
		AtlasSet<Node> label_nodes = subgraphQ.nodesTaggedWithAll("isLabel").eval().nodes();
		AtlasSet<Node> control_nodes = subgraphQ.nodesTaggedWithAll(XCSG.ControlFlowCondition).eval().nodes();
		
		AtlasSet<Node> body = new AtlasHashSet<Node>();
		AtlasSet<Node> exit = new AtlasHashSet<Node>();
		if(label_nodes.size() > 1 || control_nodes.size() > 0) {
			Q sub_label_graph = dag_no_breakQ.forward(Common.toQ(label_nodes).difference(Common.toQ(label)));
			Q sub_ctrl_graph = dag_no_breakQ.forward(Common.toQ(control_nodes));
			Q sub_diff_graph = sub_label_graph.union(sub_ctrl_graph);
//			Log.info(label.getAttr(XCSG.name).toString() + sub_label_graph.eval().nodes().size() + "|" + sub_ctrl_graph.eval().nodes().size() + "|" + sub_diff_graph.eval().nodes().size());
			subgraphQ = subgraphQ.difference(sub_diff_graph).union(sub_diff_graph.roots()).induce(dag_no_breakQ).retainEdges();	
		}
		exit = subgraphQ.leaves().eval().nodes();
		
		AtlasSet<Node> entry = new AtlasHashSet<Node>();
		entry.add(label);
		
		for(Node b : subgraphQ.eval().nodes()) {
			if(exit.contains(b)) {
				continue;
			}
			AtlasSet<Node> pred = dag_no_breakQ.predecessors(Common.toQ(b)).eval().nodes();
			for(Node p : pred) {
				if(!entry.contains(p)&&!subgraphQ.eval().nodes().contains(p)) {
					entry.add(b);
				}
			}
		}
		
		body = subgraphQ.retainNodes().difference(Common.toQ(exit)).difference(Common.toQ(entry)).eval().nodes();
		
		List<AtlasSet<Node>> l = new ArrayList<AtlasSet<Node>>();
		l.add(entry);
		l.add(body);
		l.add(exit);
		return l;
	}
	
	private static List<AtlasSet<Node>> getLabelLoop(Q cfg, Node label){
		Q cfbe=cfg.edges(XCSG.ControlFlowBackEdge).retainEdges(); //Control flow back edge
		Graph dag=cfg.differenceEdges(cfbe).retainEdges().eval(); // Control flow back edges removed
		Q dagQ = Common.toQ(dag);
		AtlasSet<Node> dagLeaves = dagQ.leaves().eval().nodes();
		
		AtlasSet<Node> loopChildNodes = Common.universe().edges(XCSG.LoopChild).forward(Common.toQ(label)).eval().nodes();
		
		AtlasSet<Node> otherLabelNodes = cfg.nodesTaggedWithAny("isLabel").difference(Common.toQ(label)).eval().nodes();
		
		Graph subgraph = dagQ.between(Common.toQ(loopChildNodes), Common.toQ(dagLeaves)).difference(dagQ.between(Common.toQ(otherLabelNodes), Common.toQ(dagLeaves))).union(Common.toQ(otherLabelNodes)).eval();
		
		subgraph = Common.toQ(subgraph).induce(cfg).retainEdges().eval();
		
		Q subgraphQ = Common.toQ(subgraph);
		
		AtlasSet<Node> body = new AtlasHashSet<Node>();
		AtlasSet<Node> exit = new AtlasHashSet<Node>();
		
		exit = subgraphQ.leaves().eval().nodes();
		
		AtlasSet<Node> entry = new AtlasHashSet<Node>();
		entry.add(label);
		
		for(Node b : subgraphQ.eval().nodes()) {
			if(exit.contains(b)) {
				continue;
			}
			AtlasSet<Node> pred = cfg.predecessors(Common.toQ(b)).eval().nodes();
			for(Node p : pred) {
				if(!entry.contains(p)&&!subgraphQ.eval().nodes().contains(p)) {
					entry.add(b);
				}
			}
		}
		
		body = subgraphQ.retainNodes().difference(Common.toQ(exit)).difference(Common.toQ(entry)).eval().nodes();
		
		List<AtlasSet<Node>> l = new ArrayList<AtlasSet<Node>>();
		l.add(entry);
		l.add(body);
		l.add(exit);
		return l;
	}
	
	private static List<AtlasSet<Node>> getDoWhile(Q cfg, Node node){
		Q cfbe=cfg.edges(XCSG.ControlFlowBackEdge).retainEdges(); //Control flow back edge
		Graph dag=cfg.differenceEdges(cfbe).retainEdges().eval(); // Control flow back edges removed
		
		Q dagQ = Common.toQ(dag);
		AtlasSet<Node> dagLeaves = dagQ.leaves().eval().nodes();
		
		AtlasSet<Node> moduleLabels = cfg.nodes("isLabel").difference(cfg.nodesTaggedWithAny(XCSG.Loop)).eval().nodes();
		
		AtlasSet<Node> exitNode = new AtlasHashSet<Node>(); // initialize the exit node
		
		
		for(Edge e : cfbe.eval().edges()) { // for all control flow back edges, find the one with current entry node
			if(cfg.successorsOn(Common.toQ(e)).eval().nodes().contains(node)) {
				// if the CFBE contains the current entry node, the predecessor would be the corresponding do while node
				// the next node on DAG would be the legal exit point
				exitNode = dagQ.forwardStep(cfg.predecessorsOn(Common.toQ(e)).retainNodes()).eval().nodes();
				break;
			}
		}
		
		List<AtlasSet<Node>> l = new ArrayList<AtlasSet<Node>>();
		
		if(exitNode.size() == 0) { // if no exit node is found, return empty list
			return l;
		}
		
		Q subgraph = dagQ.between(Common.toQ(node), Common.toQ(dagLeaves))
				.difference(dagQ.between(Common.toQ(exitNode), Common.toQ(dagLeaves)))
				.difference(dagQ.between(Common.toQ(moduleLabels), Common.toQ(dagLeaves)))
				.retainNodes().union(Common.toQ(exitNode))
				.induce(cfg).retainEdges();
		
		AtlasSet<Node> body = new AtlasHashSet<Node>();
		AtlasSet<Node> exit = new AtlasHashSet<Node>();
		
		exit = subgraph.leaves().eval().nodes();
		
		AtlasSet<Node> entry = new AtlasHashSet<Node>();
		entry.add(node);
		
		for(Node b : subgraph.eval().nodes()) {
			if(exit.contains(b)) {
				continue;
			}
			AtlasSet<Node> pred = cfg.predecessors(Common.toQ(b)).eval().nodes();
			for(Node p : pred) {
				if(!entry.contains(p)&&!subgraph.eval().nodes().contains(p)) {
					entry.add(b);
				}
			}
		}
		
		body = subgraph.retainNodes().difference(Common.toQ(exit)).difference(Common.toQ(entry)).eval().nodes();
		
		l.add(entry);
		l.add(body);
		l.add(exit);
		return l;
	}
	
	public static void analyze(Q cfg) {
		
	}
}
