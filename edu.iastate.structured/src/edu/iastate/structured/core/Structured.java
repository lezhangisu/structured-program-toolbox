package edu.iastate.structured.core;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import com.ensoftcorp.atlas.core.db.graph.Node;
import com.ensoftcorp.atlas.core.db.set.AtlasHashSet;
import com.ensoftcorp.atlas.core.db.set.AtlasSet;
import com.ensoftcorp.atlas.core.query.Q;
import com.ensoftcorp.atlas.core.xcsg.XCSG;
import com.ensoftcorp.atlas.java.core.script.Common;
import com.ensoftcorp.open.commons.algorithms.DominanceAnalysis;
import com.ensoftcorp.open.commons.algorithms.UniqueEntryExitControlFlowGraph;

import edu.iastate.structured.log.Log;

import com.ensoftcorp.atlas.core.db.set.AtlasSet;
import com.ensoftcorp.atlas.core.db.graph.Graph;
import com.ensoftcorp.atlas.core.db.graph.Node;
import com.ensoftcorp.atlas.core.db.graph.Edge;

public class Structured {
	private static Map<Node, List<AtlasSet<Node>>> map_subgraphs = new HashMap<Node, List<AtlasSet<Node>>>(); // format: <Node controlFlowCondition, List<Q entry, Q body, Q exit> >
	private static boolean DLI_done = false;
	//	private static Map<Node, Node> map_parent = new HashMap<Node, Node>(); // format: <ChildNode, ParentNode>
	
	public static Graph test(Graph cfg, Node node) {
		Q cfgQ = Common.toQ(cfg);
		List<AtlasSet<Node>> l = getIfBlock(cfg, node);
		return Common.toQ(l.get(0)).union(Common.toQ(l.get(1))).union(Common.toQ(l.get(2))).induce(cfgQ).eval();

		
	}
	
	public static Graph test(Graph cfg) {
//		return computeDominanceTree(cfg);
//		Q cfbe=cfg.edges(XCSG.ControlFlowBackEdge).retainEdges(); //Control flow back edge
//		Graph dag=cfg.differenceEdges(cfbe).retainEdges().eval();
		return removeGotoEdge(cfg);
//		return dag;
	}
	
	private static Graph removeGotoEdge(Graph cfg) {
		Q cfgQ = Common.toQ(cfg);
		Q cfbe=cfgQ.edges(XCSG.ControlFlowBackEdge).retainEdges(); //Control flow back edge
		Graph dag=cfgQ.differenceEdges(cfbe).retainEdges().eval(); // Control flow back edges removed
		Q dagQ = Common.toQ(dag);
		
		AtlasSet<Node> gotoNodes = cfgQ.nodes(XCSG.GotoStatement).eval().nodes();
		AtlasSet<Node> labelNodes = cfgQ.nodes("isLabel").eval().nodes();
		AtlasSet<Node> multiEntryLabelNodes = new AtlasHashSet<Node>();
		for(Node n : labelNodes) {
			if(cfgQ.predecessors(Common.toQ(n)).eval().nodes().size()>1) {
				multiEntryLabelNodes.add(n);
			}
		}
		if(multiEntryLabelNodes.isEmpty()) {
			return cfgQ.eval();
		}
		AtlasSet<Edge> gotoEdges = dagQ.between(Common.toQ(gotoNodes), Common.toQ(multiEntryLabelNodes)).retainEdges().eval().edges();
		return cfgQ.differenceEdges(Common.toQ(gotoEdges)).eval();
	}

	private static Graph computeDominanceTree(Graph graph) {
		Q graphQ = Common.toQ(graph);
		AtlasSet<Node> graphRoots = graphQ.roots().eval().nodes();
		AtlasSet<Node> graphLeaves = graphQ.leaves().eval().nodes();
		
		UniqueEntryExitControlFlowGraph uGraph = new UniqueEntryExitControlFlowGraph(graph, graphRoots, graphLeaves);
		Graph idomTree = DominanceAnalysis.computeDominanceTree(uGraph);
		
		AtlasSet<Node> comEntryExit = Common.toQ(idomTree).nodes("UniqueEntryExitCFG_Master_Entry","UniqueEntryExitCFG_Master_Exit").eval().nodes();
		
		Graph cleanIdomTree = Common.toQ(idomTree).difference(Common.toQ(comEntryExit)).induce(Common.toQ(idomTree)).eval();
		
		return cleanIdomTree;
	}
	
	private static List<AtlasSet<Node>> getIfBlock(Graph cfg, Node node){
		Q cfgQ = Common.toQ(cfg);
		Q cfbe=cfgQ.edges(XCSG.ControlFlowBackEdge).retainEdges(); //Control flow back edge
		Graph dag=cfgQ.differenceEdges(cfbe).retainEdges().eval(); // Control flow back edges removed
		Q dagQ = Common.toQ(dag);
		AtlasSet<Node> dagLeaves = dagQ.leaves().eval().nodes();
		
		// collect branch nodes
		AtlasSet<Node> branchNodes = cfgQ.successors(Common.toQ(node)).eval().nodes();
		
		// check if the false leave is a control flow back edge
		AtlasSet<Edge> cfbe_false_edge = cfgQ.forwardStep(Common.toQ(node)).selectEdge(XCSG.conditionValue, "false", false).retainEdges()
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
		if(intersectionNodeSet.isEmpty()) {
			subgraph = dagQ.forward(Common.toQ(branchNodes)).eval();
		}else {
			subgraph = dagQ.between(Common.toQ(branchNodes), Common.toQ(dagLeaves)).
					difference(intersection).union(intersection.induce(dagQ).roots()).eval();
		}
		
		// get dominance tree
		Graph idomTree = computeDominanceTree(removeGotoEdge(dag));
		
		// check if all nodes are dominated by the control statement
		AtlasSet<Node> redundantNodes = new AtlasHashSet<Node>();
		for(Node body_node : subgraph.nodes()) {
			if(!Common.toQ(idomTree).forward(Common.toQ(body_node)).eval().nodes().contains(node)) {
				redundantNodes.add(body_node);
			}
		}
		
		subgraph = Common.toQ(subgraph).difference(Common.toQ(redundantNodes))
				.union(Common.toQ(node)).union(Common.toQ(redundantNodes).induce(cfgQ).roots())
				.induce(cfgQ).retainEdges().eval();
		
		
		
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
	
	private static List<AtlasSet<Node>> getSwitchBlock(Graph cfg, Node node){
		Q cfgQ = Common.toQ(cfg);
		Q cfbe=cfgQ.edges(XCSG.ControlFlowBackEdge).retainEdges(); //Control flow back edge
		Graph dag=cfgQ.differenceEdges(cfbe).retainEdges().eval(); // Control flow back edges removed
		Q dagQ = Common.toQ(dag);
		AtlasSet<Node> dagLeaves = dagQ.leaves().eval().nodes();
		
		// collect branch nodes
		AtlasSet<Node> branchNodes = cfgQ.successors(Common.toQ(node)).eval().nodes();
		
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
		if(intersectionNodeSet.isEmpty()) {
			subgraph = dagQ.between(Common.toQ(branchNodes), Common.toQ(dagLeaves)).eval();
		}else {
			subgraph = dagQ.between(Common.toQ(branchNodes), Common.toQ(dagLeaves)).
					difference(intersection).union(intersection.induce(dagQ).roots()).eval();
		}
		
		// get dominance tree
		Graph idomTree = computeDominanceTree(removeGotoEdge(cfg));
		
		// check if all nodes are dominated by the control statement
		AtlasSet<Node> redundantNodes = new AtlasHashSet<Node>();
		for(Node body_node : subgraph.nodes()) {
			if(!Common.toQ(idomTree).forward(Common.toQ(body_node)).eval().nodes().contains(node)) {
				redundantNodes.add(body_node);
			}
		}
		
		subgraph = Common.toQ(subgraph).difference(Common.toQ(redundantNodes))
				.union(Common.toQ(node)).union(Common.toQ(redundantNodes).induce(cfgQ).roots())
				.induce(cfgQ).retainEdges().eval();
		
		
		AtlasSet<Node> subgraph_exit = Common.toQ(subgraph).leaves().eval().nodes();
		
		AtlasSet<Node> caseLabelExit = Common.toQ(subgraph_exit).nodes(XCSG.CaseLabel).eval().nodes();
		
		if(!caseLabelExit.isEmpty()) {
			AtlasSet<Node> case2leave = dagQ.forward(Common.toQ(caseLabelExit)).eval().nodes();
			AtlasSet<Node> nonCase2leave = dagQ.forward(Common.toQ(subgraph_exit).difference(Common.toQ(caseLabelExit))).eval().nodes();
			AtlasSet<Node> case_noncase_intersection = Common.toQ(case2leave).intersection(Common.toQ(nonCase2leave)).eval().nodes();
			Graph case_noncase_intersectionGraph = Common.toQ(case_noncase_intersection).induce(dagQ).eval();
			subgraph = dagQ.forward(Common.toQ(node)).difference(dagQ.forward(Common.toQ(case_noncase_intersectionGraph).roots()))
					.union(Common.toQ(case_noncase_intersectionGraph).roots()).retainEdges().eval();
		}
		
		AtlasSet<Node> subgraph_entry = Common.toQ(node).eval().nodes();
		subgraph_exit = Common.toQ(subgraph).leaves().eval().nodes();
		AtlasSet<Node> subgraph_body = Common.toQ(subgraph).difference(Common.toQ(subgraph_entry)).difference(Common.toQ(subgraph_exit)).eval().nodes();
		
		List<AtlasSet<Node>> return_list = new ArrayList<AtlasSet<Node>>();
		
		return_list.add(subgraph_entry);
		return_list.add(subgraph_body);
		return_list.add(subgraph_exit);
		
		return return_list;
	}
	
	private static List<AtlasSet<Node>> getLoopBlock(Graph cfg, Node node){
		Q cfgQ = Common.toQ(cfg);
		Q cfbe=cfgQ.edges(XCSG.ControlFlowBackEdge).retainEdges(); //Control flow back edge
		Graph dag=cfgQ.differenceEdges(cfbe).retainEdges().eval(); // Control flow back edges removed
		Q dagQ = Common.toQ(dag);
//		AtlasSet<Node> dagLeaves = dagQ.leaves().eval().nodes();
		
		AtlasSet<Edge> falseEdge = cfgQ.forwardStep(Common.toQ(node)).
				selectEdge(XCSG.conditionValue, "false", false).eval().edges(); // retainEdges to exclude isolated nodes

		AtlasSet<Edge> trueEdge = cfgQ.forwardStep(Common.toQ(node)).
				selectEdge(XCSG.conditionValue, "true", true).eval().edges();
		
		// get false node
		Node falseNode = Common.toQ(falseEdge).leaves().eval().nodes().getFirst();
		
		// get true node
		Node trueNode = Common.toQ(trueEdge).leaves().eval().nodes().getFirst();
		
		// get label nodes
//		AtlasSet<Node> labelNode = cfg.nodesTaggedWithAny("isLabel").eval().nodes();
		
		// label stopping node
//		AtlasSet<Node> labelStopNode = Common.toQ(labelNode).difference(cfg.nodesTaggedWithAny(XCSG.Loop)).eval().nodes();

		// Compute the nodes in control block
		AtlasSet<Node> graphNodeSet = new AtlasHashSet<Node>();
		
		graphNodeSet = dagQ.forward(Common.toQ(trueNode))
				.difference(dagQ.forward(Common.toQ(falseNode)))
				.union(Common.toQ(node)).union(Common.toQ(falseNode))
				.eval().nodes();
		
//		graphNodeSet = dagQ.between(Common.toQ(trueNode), Common.toQ(dagLeaves))
//				.difference(dagQ.between(Common.toQ(falseNode), Common.toQ(dagLeaves)))
//				.union(Common.toQ(node)).union(Common.toQ(falseNode))
//				.eval().nodes();
		
		// generate graph
		Graph subgraph = Common.toQ(graphNodeSet).induce(cfgQ).eval();
		
		// get exit nodes
		AtlasSet<Node> subgraph_exit = Common.toQ(subgraph).leaves().eval().nodes();

		// get legal entry nodes
		AtlasSet<Node> subgraph_entry = Common.toQ(node).eval().nodes();

		// pick up other illegal entry nodes
		AtlasSet<Node> illegal_entry_set = new AtlasHashSet<Node>();

		for(Node n : Common.toQ(subgraph).difference(Common.toQ(subgraph_exit)).eval().nodes()) {
			for(Node ent : cfgQ.predecessors(Common.toQ(n)).eval().nodes()) {
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
	
	private static List<AtlasSet<Node>> getLabelModule(Graph cfg, Node label){
		Q cfgQ = Common.toQ(cfg);
		Q cfbe=cfgQ.edges(XCSG.ControlFlowBackEdge).retainEdges(); //Control flow back edge
		Graph dag=cfgQ.differenceEdges(cfbe).retainEdges().eval(); // Control flow back edges removed
		Q dagQ = Common.toQ(dag);
		
		Q break_nodes = cfgQ.nodes(XCSG.Break);
		Q break_edges = cfgQ.forwardStep(break_nodes).retainEdges();
		
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
	
	private static List<AtlasSet<Node>> getLabelLoop(Graph cfg, Node label){
		Q cfgQ = Common.toQ(cfg);
		Q cfbe=cfgQ.edges(XCSG.ControlFlowBackEdge).retainEdges(); //Control flow back edge
		Graph dag=cfgQ.differenceEdges(cfbe).retainEdges().eval(); // Control flow back edges removed
		Q dagQ = Common.toQ(dag);
		AtlasSet<Node> dagLeaves = dagQ.leaves().eval().nodes();
		
		AtlasSet<Node> loopChildNodes = Common.universe().edges(XCSG.LoopChild).forward(Common.toQ(label)).eval().nodes();
		
		AtlasSet<Node> otherLabelNodes = cfgQ.nodesTaggedWithAny("isLabel").difference(Common.toQ(label)).eval().nodes();
		
		Graph subgraph = dagQ.between(Common.toQ(loopChildNodes), Common.toQ(dagLeaves)).difference(dagQ.between(Common.toQ(otherLabelNodes), Common.toQ(dagLeaves))).union(Common.toQ(otherLabelNodes)).eval();
		
		subgraph = Common.toQ(subgraph).induce(cfgQ).retainEdges().eval();
		
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
			AtlasSet<Node> pred = cfgQ.predecessors(Common.toQ(b)).eval().nodes();
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
	
	private static List<AtlasSet<Node>> getDoWhile(Graph cfg, Node node){
		Q cfgQ = Common.toQ(cfg);
		Q cfbe=cfgQ.edges(XCSG.ControlFlowBackEdge).retainEdges(); //Control flow back edge
		Graph dag=cfgQ.differenceEdges(cfbe).retainEdges().eval(); // Control flow back edges removed
		
		Q dagQ = Common.toQ(dag);
		AtlasSet<Node> dagLeaves = dagQ.leaves().eval().nodes();
		
		AtlasSet<Node> moduleLabels = cfgQ.nodes("isLabel").difference(cfgQ.nodesTaggedWithAny(XCSG.Loop)).eval().nodes();
		
		AtlasSet<Node> exitNode = new AtlasHashSet<Node>(); // initialize the exit node
		
		
		for(Edge e : cfbe.eval().edges()) { // for all control flow back edges, find the one with current entry node
			if(cfgQ.successorsOn(Common.toQ(e)).eval().nodes().contains(node)) {
				// if the CFBE contains the current entry node, the predecessor would be the corresponding do while node
				// the next node on DAG would be the legal exit point
				exitNode = dagQ.forwardStep(cfgQ.predecessorsOn(Common.toQ(e)).retainNodes()).eval().nodes();
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
				.induce(cfgQ).retainEdges();
		
		AtlasSet<Node> body = new AtlasHashSet<Node>();
		AtlasSet<Node> exit = new AtlasHashSet<Node>();
		
		exit = subgraph.leaves().eval().nodes();
		
		AtlasSet<Node> entry = new AtlasHashSet<Node>();
		entry.add(node);
		
		for(Node b : subgraph.eval().nodes()) {
			if(exit.contains(b)) {
				continue;
			}
			AtlasSet<Node> pred = cfgQ.predecessors(Common.toQ(b)).eval().nodes();
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
	
	public static boolean runDLI() {
		Log.info("DLI Starts");
		com.ensoftcorp.open.jimple.commons.loops.DecompiledLoopIdentification.recoverLoops();
		Log.info("DLI Finished");
		return true;
	}
	
	public static void analyze(Graph cfg) {
//		Log.info("Analysis Begins");
		Q cfgQ = Common.toQ(cfg);
		//1. get selectable nodes (DLI loop entry, control nodes, labels) and tag them
		map_subgraphs.clear();
//		map_parent.clear();
//		Log.info("Analyze-DLI");
		
		// run DLI
		if(!DLI_done) {
			DLI_done = runDLI();
		}
		
		Log.info("Tag Selectable Begins");
		// initialize a set with label nodes, DLI loop entry nodes, control statement nodes
		AtlasSet<Node> selectable = cfgQ.nodesTaggedWithAny("isLabel", XCSG.Loop, XCSG.ControlFlowIfCondition, XCSG.ControlFlowSwitchCondition).eval().nodes();

		// tag selectable nodes
		for(Node s : selectable) {
			s.tag("STRUCT_SELECTABLE");
		}
		
		//2. for each selectable node, get block or module, store them in map
//		Q cfbe=cfgQ.edges(XCSG.ControlFlowBackEdge).retainEdges(); //Control flow back edge
//		Q dagQ=cfgQ.differenceEdges(cfbe); // Control flow back edges removed
		
//		Log.info("Analyze-get block");
		for(Node node : selectable) {
			Log.info("Proceccing block " + node.getAttr(XCSG.name));
			if(node.taggedWith("isLabel")&&!node.taggedWith(XCSG.Loop)) { // straight forward label
//				Log.info(node.getAttr(XCSG.name) + " getModule");
				map_subgraphs.put(node, getLabelModule(cfg, node));
			}else if(node.taggedWith("isLabel")&&node.taggedWith(XCSG.Loop)) { // label creates loop
				node.tag("LoopByLabel");
				map_subgraphs.put(node, getLabelLoop(cfg, node));
			}else if(node.taggedWith("isDoWhileLoop")) {  // do while loop
				map_subgraphs.put(node, getDoWhile(cfg, node));
			}else if(node.taggedWith(XCSG.ControlFlowIfCondition)) { // if 
				map_subgraphs.put(node, getIfBlock(cfg, node));
			}else if(node.taggedWith(XCSG.ControlFlowLoopCondition)) { // while, for loop
				map_subgraphs.put(node, getLoopBlock(cfg, node));
			}else if(node.taggedWith(XCSG.ControlFlowSwitchCondition)) { // Switch
				map_subgraphs.put(node, getSwitchBlock(cfg, node));
			}
			//for each module or block, update parent relationships 
//			Log.info("Analyze-get block " + node.getAttr(XCSG.name));
		}
		
		//3. for each nested module or block, update exit points based on parents' exit points
		// start with nodes with no parents (ancestor nodes)
//		Set<Node> no_parents = new HashSet<Node>();
//		Set<Node> previous_no_parents = new HashSet<Node>();
		
		// initialize node set with node has no parents (find out ancestor nodes)
//		no_parents.addAll(map_subgraphs.keySet()); // add all selectable nodes
//		no_parents.removeAll(map_parent.keySet()); // remove nodes that have parents

	}
	
	public static Map<Node, Node> getParentMap(Graph cfg) {
		Q cfgQ = Common.toQ(cfg);
		if(cfgQ.nodes("STRUCT_SELECTABLE").eval().nodes().isEmpty()) {
			analyze(cfg);
		}
		Map<Node, Node> map_parent = new HashMap<Node, Node>();
		for(Node n : map_subgraphs.keySet()) {
			for(Node m : map_subgraphs.get(n).get(1)) {
				map_parent.put(m, n);
			}
		}
		return map_parent;
	}
	
	public static Map<Node, List<AtlasSet<Node>>> getMap(){
		return map_subgraphs;
	}
	
	public static AtlasSet<Node> getSelectable(Q cfg){
		return cfg.nodesTaggedWithAll("STRUCT_SELECTABLE").eval().nodes();
	}
}
