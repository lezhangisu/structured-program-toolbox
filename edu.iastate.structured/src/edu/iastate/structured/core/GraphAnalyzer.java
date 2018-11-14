package edu.iastate.structured.core;

import java.util.List;
import java.util.Map;
import java.util.Set;
import java.awt.Color;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

import com.ensoftcorp.atlas.core.db.graph.Graph;
import com.ensoftcorp.atlas.core.db.graph.Node;
import com.ensoftcorp.atlas.core.db.graph.Edge;
import com.ensoftcorp.atlas.core.db.set.AtlasHashSet;
import com.ensoftcorp.atlas.core.db.set.AtlasSet;
import com.ensoftcorp.atlas.core.index.common.SourceCorrespondence;
import com.ensoftcorp.atlas.core.markup.Markup;
import com.ensoftcorp.atlas.core.markup.MarkupProperty;
import com.ensoftcorp.atlas.core.query.Q;
import com.ensoftcorp.atlas.core.script.Common;
import com.ensoftcorp.atlas.core.script.CommonQueries;
import com.ensoftcorp.atlas.core.xcsg.XCSG;
import com.ensoftcorp.atlas.ui.viewer.graph.DisplayUtil;
import com.ensoftcorp.atlas.ui.viewer.graph.SaveUtil;

import edu.iastate.structured.core.VerificationProperties;
import edu.iastate.structured.log.Log;

/**
* This program checks if a given function or all functions in mapped workspace are structured
* It parses through all the control flow condition nodes and obtain the subgraph under them
* If the subgraph has more than one entries, it is unstructured.
*
* @author Le Zhang
*/
public class GraphAnalyzer {
	private static Map<Node, List<AtlasSet<Node>>> map_subgraphs = new HashMap<Node, List<AtlasSet<Node>>>(); // format: <Node controlFlowCondition, List<Q entry, Q body, Q exit> >
	private static Map<Node, Node> map_parent = new HashMap<Node, Node>(); // format: <ChildNode, ParentNode>

	
	/**
	 * The name pattern for the directory containing the graphs for the processed goto.
	 * <p>
	 * 1- The {@link SourceCorrespondence}.
	 */
	private static final String GOTO_GRAPH_DIRECTORY_NAME_PATTERN = "labelModule_graphs";
	
	/**
	 * The directory where the verification graphs for the processed lock to be stored}.
	 */
	private static File currentgotoGraphsOutputDirectory;
	
	/**
	 * The root output directory for all the graphs. The current class with create a directory with {@link #currentLockGraphsOutputDirectory}
	 * to store all generated graph per processed lock.
	 */
	private Path graphsOutputDirectory;
	
	/**
	 * The name pattern for the CFG graph.
	 * <p>
	 * The following is the parts of the name:
	 * 1- The method name corresponding to the CFG.
	 */
	private static final String CFG_GRAPH_FILE_NAME_PATTERN = "%s-CFG@%s@%s@%s";
	private static final String PCG_GRAPH_FILE_NAME_PATTERN = "%s-PCG@%s@%s@%s";
	
	public GraphAnalyzer()
	{
		this.graphsOutputDirectory = VerificationProperties.getGraphsOutputDirectory();
		
	}
	
	private static void saveDisplayCFG(Graph cfgGraph, int num, String sourceFile, String methodName, Markup markup, boolean displayGraphs) { 
        if(displayGraphs){
            DisplayUtil.displayGraph(markup, cfgGraph);
        }
            
        try{
            String cfgFileName = String.format(CFG_GRAPH_FILE_NAME_PATTERN, num, sourceFile, methodName, VerificationProperties.getGraphImageFileNameExtension());
            SaveUtil.saveGraph(new File(currentgotoGraphsOutputDirectory, cfgFileName), cfgGraph, markup).join();
        } catch (InterruptedException e) {}
            
    }	
	
	private static void saveDisplayPCG(Graph pcgGraph, int num, String sourceFile, String methodName, Markup markup, boolean displayGraphs) { 
        if(displayGraphs){
            DisplayUtil.displayGraph(markup, pcgGraph);
        }
            
        try{
            String pcgFileName = String.format(PCG_GRAPH_FILE_NAME_PATTERN, num, sourceFile, methodName, VerificationProperties.getGraphImageFileNameExtension());
            SaveUtil.saveGraph(new File(currentgotoGraphsOutputDirectory, pcgFileName), pcgGraph, markup).join();
        } catch (InterruptedException e) {}
            
    }
	
	private void createDirectory(){
        String containingDirectoryName = String.format(GOTO_GRAPH_DIRECTORY_NAME_PATTERN);
        currentgotoGraphsOutputDirectory = this.graphsOutputDirectory.resolve(containingDirectoryName).toFile();
        if(!currentgotoGraphsOutputDirectory.exists())
        {
        if(!currentgotoGraphsOutputDirectory.mkdirs()){
            Log.info("Cannot create directory:" + currentgotoGraphsOutputDirectory.getAbsolutePath());
        }
        }
    }
	
	private static Node getDeclarativeParent(Node node) {
		AtlasSet<Node> parentNodes = Common.toQ(node).parent().eval().nodes();
		if(parentNodes.size() > 1){
			throw new IllegalArgumentException("Multiple declarative parents!");
		}
		return parentNodes.one();
	}
	
	public static String getQualifiedName(Node node, String...stopAfterTags) {
		if(node == null){
			throw new IllegalArgumentException("Node is null!");
		}
		String result = node.attr().get(XCSG.name).toString();
		Node parent = getDeclarativeParent(node);
		boolean qualified = false;
		while (parent != null && !qualified) {
			for(String stopAfterTag : stopAfterTags){
				if(parent.taggedWith(stopAfterTag)){
					qualified = true;
				}
			}
			String prefix = parent.attr().get(XCSG.name).toString();
			if(!prefix.equals("")){
				result = parent.attr().get(XCSG.name) + "." + result;
			}
			parent = getDeclarativeParent(parent);
		}
		return result;
	}
	
	public static String getQualifiedFunctionName(Node function) {
		if(function == null){
			throw new IllegalArgumentException("Function is null!");
		}
		if(!function.taggedWith(XCSG.Function)){
			throw new IllegalArgumentException("Function parameter is not a function!");
		}
		return getQualifiedName(function, XCSG.Package);
	}
	

	public static List<AtlasSet<Node>> getModule(Q cfg, Node label){
//		Q cfg_leaves = cfg.leaves();
		Q cfbe=cfg.edges(XCSG.ControlFlowBackEdge).retainEdges(); //Control flow back edge
		Q dag=cfg.differenceEdges(cfbe).retainEdges(); // Control flow back edges removed
		Q break_nodes = cfg.nodes(XCSG.Break);
		Q break_edges = cfg.forwardStep(break_nodes).retainEdges();
		
		Q dag_no_break = dag.differenceEdges(break_edges).retainEdges();
		
		Q subgraph = dag_no_break.forward(Common.toQ(label));
		Q label_nodes = subgraph.nodesTaggedWithAll("isLabel");
		Q control_nodes = subgraph.nodesTaggedWithAll(XCSG.ControlFlowCondition);
		
		AtlasSet<Node> body = new AtlasHashSet<Node>();
		AtlasSet<Node> exit = new AtlasHashSet<Node>();
		if(label_nodes.eval().nodes().size() > 1 || control_nodes.eval().nodes().size() > 0) {
			Q sub_label_graph = dag_no_break.forward(label_nodes.difference(Common.toQ(label)));
			Q sub_ctrl_graph = dag_no_break.forward(control_nodes);
			Q sub_diff_graph = sub_label_graph.union(sub_ctrl_graph);
//			Log.info(label.getAttr(XCSG.name).toString() + sub_label_graph.eval().nodes().size() + "|" + sub_ctrl_graph.eval().nodes().size() + "|" + sub_diff_graph.eval().nodes().size());
			subgraph = subgraph.difference(sub_diff_graph).union(sub_diff_graph.roots()).induce(dag_no_break).retainEdges();	
		}
		exit = subgraph.leaves().eval().nodes();
		
		AtlasSet<Node> entry = new AtlasHashSet<Node>();
		entry.add(label);
		
		for(Node b : subgraph.eval().nodes()) {
			if(exit.contains(b)) {
				continue;
			}
			AtlasSet<Node> pred = dag_no_break.predecessors(Common.toQ(b)).eval().nodes();
			for(Node p : pred) {
				if(!entry.contains(p)&&!subgraph.eval().nodes().contains(p)) {
					entry.add(b);
				}
			}
		}
		
		body = subgraph.retainNodes().difference(Common.toQ(exit)).difference(Common.toQ(entry)).eval().nodes();
		
		List<AtlasSet<Node>> l = new ArrayList<AtlasSet<Node>>();
		l.add(entry);
		l.add(body);
		l.add(exit);
		return l;
	}
	
	public static List<AtlasSet<Node>> getLabelLoop(Q cfg, Node label){
		Q cfbe=cfg.edges(XCSG.ControlFlowBackEdge).retainEdges(); //Control flow back edge
		Q dag=cfg.differenceEdges(cfbe).retainEdges(); // Control flow back edges removed
		
		Q loop_children_nodes = Common.universe().edges(XCSG.LoopChild).forward(Common.toQ(label)).retainNodes();
		
		Q otherLabels = cfg.nodesTaggedWithAny("isLabel").difference(Common.toQ(label));
		
		Q subgraph = dag.between(loop_children_nodes, dag.leaves()).difference(dag.between(otherLabels, dag.leaves())).union(otherLabels);
		
		subgraph = subgraph.induce(cfg).retainEdges();
		
		AtlasSet<Node> body = new AtlasHashSet<Node>();
		AtlasSet<Node> exit = new AtlasHashSet<Node>();
		
		exit = subgraph.leaves().eval().nodes();
		
		AtlasSet<Node> entry = new AtlasHashSet<Node>();
		entry.add(label);
		
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
		
		List<AtlasSet<Node>> l = new ArrayList<AtlasSet<Node>>();
		l.add(entry);
		l.add(body);
		l.add(exit);
		return l;
	}
	
	public static List<AtlasSet<Node>> getDoWhile(Q cfg, Node node){
		Q cfbe=cfg.edges(XCSG.ControlFlowBackEdge).retainEdges(); //Control flow back edge
		Q dag=cfg.differenceEdges(cfbe).retainEdges(); // Control flow back edges removed
		
		Q moduleLabels = cfg.nodesTaggedWithAny("isLabel").difference(cfg.nodesTaggedWithAny(XCSG.Loop));
		
		Q exitNode = null; // initialize the exit node
		
		
		for(Edge e : cfbe.eval().edges()) { // for all control flow back edges, find the one with current entry node
			if(cfg.successorsOn(Common.toQ(e)).eval().nodes().contains(node)) {
				// if the CFBE contains the current entry node, the predecessor would be the corresponding do while node
				// the next node on DAG would be the legal exit point
				exitNode = dag.forwardStep(cfg.predecessorsOn(Common.toQ(e)).retainNodes());
				break;
			}
		}
		
		List<AtlasSet<Node>> l = new ArrayList<AtlasSet<Node>>();
		
		if(exitNode == null) { // if no exit node is found, return empty list
			return l;
		}
		
		Q subgraph = dag.between(Common.toQ(node), dag.leaves())
				.difference(dag.between(exitNode, dag.leaves()))
				.difference(dag.between(moduleLabels, dag.leaves()))
				.retainNodes().union(exitNode)
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
	
	public static List<AtlasSet<Node>> getBlock(Q cfg, Node node){
		Q cf_condition = Common.toQ(node);
		Q cfbe=cfg.edges(XCSG.ControlFlowBackEdge).retainEdges(); //Control flow back edge
		Q dag=cfg.differenceEdges(cfbe); // Control flow back edges removed

		// Initialize the subgraph queries
		Q subgraph_q = Common.empty();
		Q subgraph_exit_q = Common.empty();
		Q subgraph_entry_q = Common.empty();

		// if selected node is a loop, exit will be the false branch
		if (cf_condition.eval().nodes().getFirst().taggedWith(XCSG.ControlFlowLoopCondition)) {
			// get false edge
			Q falseEdge = cfg.forwardStep(cf_condition).
					selectEdge(XCSG.conditionValue, "false", false).retainEdges(); // retainEdges to exclude isolated nodes

			// get false node
			Q falseNode = falseEdge.leaves();
			
			// get label nodes
			Q labelNode = cfg.nodesTaggedWithAny("isLabel");
			
			// label stopping node
			Q labelStopNode = labelNode.difference(cfg.nodesTaggedWithAny(XCSG.Loop));

			// get the subgraph
			subgraph_q =
					// get the part from loop condition to DAG leaves (to include the loop and return statements)
					dag.between(cf_condition, dag.leaves()).
					// get the part from loop condition to false node (to include possible break statements)
					union(dag.between(cf_condition, falseNode)).
					// exclude the part from false node to DAG leaves
					difference(dag.between(falseNode, dag.leaves()).retainEdges()).
					// exclude the part from label node to DAG leaves
					difference(dag.between(labelStopNode, dag.leaves()).retainEdges()).
					// put back false node and false edge to make the subgraph complete
					union(falseNode).union(falseEdge).union(labelNode).retainEdges();

			// use induce(cfg) to add missing edges from CFG so we have complete subgraph
			subgraph_q = subgraph_q.induce(cfg).retainEdges();

			// get exit nodes
			subgraph_exit_q = subgraph_q.leaves();

			// get legal entry nodes
			subgraph_entry_q = cf_condition;

			// pick up other illegal entry nodes
			AtlasSet<Node> illegal_entry_set = new AtlasHashSet<Node>();

			for(Node n : subgraph_q.difference(subgraph_exit_q).eval().nodes()) {
				for(Node ent : cfg.predecessors(Common.toQ(n)).eval().nodes()) {
					if(!subgraph_q.eval().nodes().contains(ent)) {
						illegal_entry_set.add(n);
					}
				}
			}
			subgraph_entry_q = subgraph_entry_q.union(Common.toQ(illegal_entry_set));

		}else{
			// Non-loop conditions (IF and SWITCH)
			// collect branch nodes
			AtlasSet<Node> branchNodes = cfg.successors(cf_condition).eval().nodes();

			// check if the false leave is a control flow back edge
			Q CFBE_false_edge = cfg.forwardStep(cf_condition).selectEdge(XCSG.conditionValue, "false", false).retainEdges()
					.edgesTaggedWithAny(XCSG.ControlFlowBackEdge);
			if(CFBE_false_edge.eval().edges().size() > 0) {
				List<AtlasSet<Node>> return_list = new ArrayList<AtlasSet<Node>>();

				return_list.add(cf_condition.eval().nodes());
				return_list.add(dag.forward(cf_condition).difference(cf_condition).eval().nodes());
				return_list.add(CFBE_false_edge.leaves().eval().nodes());

				return return_list;
			}

			// collect the paths from each branch node to DAG leaves
			List<Q> list_paths = new ArrayList<Q>();
			for(Node branch_root : branchNodes) {
				list_paths.add(dag.between(Common.toQ(branch_root), dag.leaves()));
			}

			// For every two branch paths, find if there is an intersection
			// save the common intersection to this query
			Q joint_paths = null;
			AtlasSet<Node> joint_paths_node_set = new AtlasHashSet<Node>();

			for(int i = 0; i<list_paths.size()-1; i++) {
				for(int j = i+1; j<list_paths.size(); j++) {
					// get intersections of two branches
					AtlasSet<Node> tmp_joint_paths_node_set = list_paths.get(i).intersection(list_paths.get(j)).eval().nodes();
					if(tmp_joint_paths_node_set.size()>0) {
						joint_paths_node_set.addAll(tmp_joint_paths_node_set);
					}
				}
			}
			joint_paths = Common.toQ(joint_paths_node_set);

			subgraph_q = Common.empty();

			// get subgraph nodes
			if(joint_paths == null) {
				subgraph_q = dag.between(Common.toQ(branchNodes), dag.leaves());
			}else {
				subgraph_q = dag.between(Common.toQ(branchNodes), dag.leaves()).
						difference(joint_paths).union(joint_paths.induce(dag).roots());
			}

			// complete the subgraph with edges
			subgraph_q = subgraph_q.union(cf_condition).induce(cfg).retainEdges();

			// get exit nodes
			subgraph_exit_q = subgraph_q.leaves();

			if(subgraph_exit_q.nodesTaggedWithAny(XCSG.CaseLabel).eval().nodes().size()>0) {
				Q case2leave = dag.between(subgraph_exit_q.nodesTaggedWithAny(XCSG.CaseLabel), dag.leaves());
				Q nonCase2leave = dag.between(subgraph_exit_q.difference(subgraph_exit_q.nodesTaggedWithAny(XCSG.CaseLabel)), dag.leaves());
				Q case_noncase_intersection = case2leave.intersection(nonCase2leave);
				subgraph_q = dag.between(cf_condition, dag.leaves()).difference(dag.between(case_noncase_intersection.roots(), dag.leaves()))
						.union(case_noncase_intersection.roots());
			}
			
			// collect label node but not loop label node included
			AtlasSet<Node> labelNodes = subgraph_q.nodesTaggedWithAny("isLabel").difference(cfg.nodesTaggedWithAny(XCSG.Loop)).eval().nodes();
			
			// if there are label nodes, exclude those label paths
			if(labelNodes.size() >0){
				Q labelPath = Common.empty();
				for(Node ln : labelNodes) {
					labelPath = labelPath.union(dag.between(Common.toQ(ln), dag.leaves()));
				}
				subgraph_q = subgraph_q.difference(labelPath).union(Common.toQ(labelNodes));
			}
			
			// complete the subgraph with edges again
			subgraph_q = subgraph_q.union(cf_condition).induce(cfg).retainEdges();

			// update subgraph exits
			subgraph_exit_q = subgraph_q.leaves();

			// get legal entry nodes
			subgraph_entry_q = cf_condition;

			// pick up other illegal entry nodes
			AtlasSet<Node> illegal_entry_set = new AtlasHashSet<Node>();

			for(Node n : subgraph_q.difference(subgraph_exit_q).eval().nodes()) {
				for(Node ent : cfg.predecessors(Common.toQ(n)).eval().nodes()) {
					if(!subgraph_q.eval().nodes().contains(ent)) {
						illegal_entry_set.add(n); // add illegal entry node to the set
					}
				}
			}
			subgraph_entry_q = subgraph_entry_q.union(Common.toQ(illegal_entry_set));

			// if the selected condition is not switch, it probably have a case node as entry due to case fall-through
			if(!cf_condition.eval().nodes().one().taggedWith(XCSG.ControlFlowSwitchCondition)) {
				// check for nodes labeled with "caseLabel" in the subgraph being recognized as illegal entries caused by fall-through
				Q caseNodes_entries = subgraph_entry_q.nodesTaggedWithAny(XCSG.CaseLabel);
				if(caseNodes_entries.eval().nodes().size() > 0) {
					subgraph_q =
							// exclude the paths from illegal case nodes to exits
							subgraph_q.difference(dag.between(caseNodes_entries, subgraph_exit_q)).
							// add the first case node back as exit
							union(dag.between(caseNodes_entries, subgraph_exit_q).retainEdges().roots()).
							// keep the previous exits
							union(subgraph_exit_q).induce(cfg).retainEdges();

					// update subgraph exits
					subgraph_exit_q = subgraph_q.leaves();

					// update legal entry nodes
					subgraph_entry_q = cf_condition;

					// pick up other illegal entry nodes
					illegal_entry_set.clear();

					for(Node n : subgraph_q.difference(subgraph_exit_q).eval().nodes()) {
						for(Node ent : cfg.predecessors(Common.toQ(n)).eval().nodes()) {
							if(!subgraph_q.eval().nodes().contains(ent)) {
								illegal_entry_set.add(n);
							}
						}
					}
					subgraph_entry_q = subgraph_entry_q.union(Common.toQ(illegal_entry_set));
				}
			}

		}

		AtlasSet<Node> subgraph_set = subgraph_q.retainEdges().difference(subgraph_entry_q).difference(subgraph_exit_q).eval().nodes();
		AtlasSet<Node> subgraph_entry_set = subgraph_entry_q.retainNodes().eval().nodes();
		AtlasSet<Node> subgraph_exit_set = subgraph_exit_q.retainNodes().eval().nodes();

		List<AtlasSet<Node>> return_list = new ArrayList<AtlasSet<Node>>();

		return_list.add(subgraph_entry_set);
		return_list.add(subgraph_set);
		return_list.add(subgraph_exit_set);

		return return_list;
	}
	
	/**
	* Update parent map
	 * @param Node parent, dag
	 * @return none
	 */
	private static void updateParentMap(Node parent_node, Q dag) {  // input: graph root and graph list [entry, body, exit]

		// get body nodes of this block
		Q subgraph_body_q = Common.toQ(map_subgraphs.get(parent_node).get(1));

		// update exits of nested nodes
		for(Node child : subgraph_body_q.nodesTaggedWithAny("STRUCT_SELECTABLE").eval().nodes()) {
			if(map_parent.containsKey(child)) {
				Node prev_parent = map_parent.get(child);
				// compare previous parent with current parent
				// pick the smaller sized father to be the actual parent
				if(getDistance(parent_node, child, dag) < getDistance(prev_parent, child, dag)) {

					// if smaller, update parenthood
					map_parent.put(child, parent_node);
				}
			}else {
				// no record, just update value
				map_parent.put(child, parent_node);
			}
		}
	}
	
	/**
	* Get shortest distance from node1 to node2 using BFS
	 * @param node1, node2
	 * @return int distance
	 */
	private static int getDistance(Node node1, Node node2, Q dag) {
		AtlasSet<Node> current = new AtlasHashSet<Node>();
		current.add(node1);
		int steps = 0;
		if(dag.forward(Common.toQ(node1)).eval().nodes().contains(node2)) {
			Q partDag = dag.between(Common.toQ(node1), Common.toQ(node2));
			int count = 0;
			while(!current.isEmpty()) {
				steps += 1;
				AtlasSet<Node> tmp = new AtlasHashSet<Node>();
				for(Node node : current) {
					AtlasSet<Node> tmp_nxt = partDag.successors(Common.toQ(node)).eval().nodes();
					if(tmp_nxt.contains(node2)) {
						return steps;
					}
					tmp.addAll(tmp_nxt);
				}
				current.clear();
				current.addAll(tmp);

				count++;
				if(count>1000) {
					Log.info("GetDistance() exceeds max iterations 1000 at node " + node1.getAttr(XCSG.name) + " | and node | " + node2.getAttr(XCSG.name));
					return steps;
				}
			}
		}
		return -1;
	}
	
	/**
	* Update child subgraph based on the parent's exits
	 * @param Node child, Q dag, Q cfg
	 * @return none
	 */
	private static void updateChildExits(int cnt, Node child, Q dag, Q cfg) {
		Log.info("updateChildExits()" + child.getAttr(XCSG.name));
		
		//avoid deadlock
		if(cnt == 0) {
			Log.info("updateChildExits() exceeds max recursion");
			return;
		}

		// cast to Q
		Q cf_condition = Common.toQ(child);

		// list [entry, subgraph, exits]
		List<AtlasSet<Node>> subgraph = map_subgraphs.get(child);
		
		AtlasSet<Node> oldSelectableNodes = Common.toQ(subgraph.get(1)).nodesTaggedWithAny("STRUCT_SELECTABLE").eval().nodes();

		// terminate subgraph based on exits of parent subgraph
		// if it has a parent
		if(map_parent.containsKey(child)) {

			// get parent exits
			AtlasSet<Node> parent_exits = map_subgraphs.get(map_parent.get(child)).get(2);
			// get paths starting from parent's exits
			Q extra_portion = dag.forward(Common.toQ(parent_exits)).retainNodes();

			// get subgraph body nodes
			// need to include entries because at this point some body nodes may be treated as entries
			Q subgraph_body_q = Common.toQ(subgraph.get(1)).union(Common.toQ(subgraph.get(0)));

//			AtlasSet<Node> body = subgraph_body_q.difference(extra_portion).eval().nodes();
			
			// if there is an intersection
			if(extra_portion.intersection(subgraph_body_q).eval().nodes().size() > 0) {
				
				Log.info("update subgraph " + map_parent.get(child).getAttr(XCSG.name));

				// update the subgraph body
				AtlasSet<Node> body = new AtlasHashSet<Node>();

				body.addAll(subgraph.get(1));
				body = Common.toQ(body).difference(extra_portion).eval().nodes();

				subgraph.set(1, body);

				// update exits
				AtlasSet<Node> exit = Common.toQ(subgraph.get(1)).union(cf_condition).union(Common.toQ(parent_exits)).induce(cfg).retainEdges().leaves().eval().nodes();

				subgraph.set(2, exit);

				// update the entries
				AtlasSet<Node> entry = new AtlasHashSet<Node>();
				// pick up entry nodes
				AtlasSet<Node> subgraph_body_set = Common.toQ(subgraph.get(1)).union(cf_condition).eval().nodes();
				for(Node n : subgraph_body_set) {
					for(Node ent : cfg.predecessors(Common.toQ(n)).eval().nodes()) {
						if(!subgraph_body_set.contains(ent)) {
							entry.add(n);
						}
					}
				}
				subgraph.set(0, entry);

				// update new subgraph
				map_subgraphs.put(child, subgraph);

				AtlasSet<Node> its_children = Common.toQ(subgraph.get(1)).nodesTaggedWithAny("STRUCT_SELECTABLE").eval().nodes();
				
				for(Node n : oldSelectableNodes) {
					if(its_children.contains(n)) {
						continue;
					}
					updateParent(n);
				}
				
				Log.info("child size " + its_children.size());
				if(its_children.size()>0) {
					for(Node forward_child : its_children) {
						Log.info("Parent:: " + child.getAttr(XCSG.name) + " ||Child:: " + forward_child.getAttr(XCSG.name));
						updateChildExits(cnt--, forward_child, dag, cfg);
					}
				}
			}
		}
	}
	
	/**
	* Update parent map when child need a new parent
	 * @param Node child
	 * @return none
	 */
	private static void updateParent(Node child) {
		// We assume that this child need a new parent
		Node parent = map_parent.get(child);
		if(!map_parent.containsKey(parent)) { // if no grand parents
			map_parent.remove(child); // remove this child, it now has no parents
			return;
		}
		
		boolean flag = false;
		int cnt = 0;
		while(map_parent.containsKey(parent) && cnt<100) {
			parent = map_parent.get(parent);
			
			if(map_subgraphs.get(parent).get(1).contains(child)) {
				map_parent.put(child, parent);
				flag = true;
				return;
			}
			cnt++;
		}
		
		if(!flag) {
			map_parent.remove(child);
		}
		
	}
	
	/**
	* Analyze the given CFG and parse out the code blocks
	 * @param Q cfg
	 * @return none
	 */
	public static void analyze(Q cfg) {
		//1. get selectable nodes (DLI loop entry, control nodes, labels) and tag them
		
		// run DLI
		com.ensoftcorp.open.jimple.commons.loops.DecompiledLoopIdentification.recoverLoops();

		// initialize a set with label nodes, DLI loop entry nodes, control statement nodes
		AtlasSet<Node> selectable = cfg.nodesTaggedWithAny("isLabel", XCSG.Loop, XCSG.ControlFlowCondition).eval().nodes();

		// tag selectable nodes
		for(Node s : selectable) {
			s.tag("STRUCT_SELECTABLE");
		}
		
		//2. for each selectable node, get block or module, store them in map
		Q cfbe=cfg.edges(XCSG.ControlFlowBackEdge).retainEdges(); //Control flow back edge
		Q dag=cfg.differenceEdges(cfbe); // Control flow back edges removed
		
		for(Node node : selectable) {
			if(node.taggedWith("isLabel")&&!node.taggedWith(XCSG.Loop)) { // straight forward label
//				Log.info(node.getAttr(XCSG.name) + " getModule");
				map_subgraphs.put(node, getModule(cfg, node));
			}else if(node.taggedWith("isLabel")&&node.taggedWith(XCSG.Loop)) { // label creates loop
				map_subgraphs.put(node, getLabelLoop(cfg, node));
			}else if(node.taggedWith("isDoWhileLoop")) {  // do while loop
				map_subgraphs.put(node, getDoWhile(cfg, node));
			}else { // normal IF/While/For/Switch
//				Log.info(node.getAttr(XCSG.name) + " getBlock");
				map_subgraphs.put(node, getBlock(cfg, node));
			}
			//for each module or block, update parent relationships 
			updateParentMap(node, dag);
		}
		
		//3. for each nested module or block, update exit points based on parents' exit points
		// start with nodes with no parents (ancestor nodes)
		Set<Node> no_parents = new HashSet<Node>();
		Set<Node> previous_no_parents = new HashSet<Node>();
		
		// initialize node set with node has no parents (find out ancestor nodes)
		no_parents.addAll(map_subgraphs.keySet()); // add all selectable nodes
		no_parents.removeAll(map_parent.keySet()); // remove nodes that have parents

		// update all nested subgraphs
		// while set of no parent subgraphs changes
		int count = 0;
		while(count<100 && !(previous_no_parents.size() == no_parents.size() && previous_no_parents.containsAll(no_parents))) {
			// for each subgraph with no parent
			for(Node node : no_parents) {
				// get children
				AtlasSet<Node> children = Common.toQ(map_subgraphs.get(node).get(1)).nodesTaggedWithAny("STRUCT_SELECTABLE").eval().nodes();

				// if no child, skip
				if(children.size() < 1) {
					continue;
				}

				// update child subgraph
				for(Node child : children) {
					updateChildExits(100, child, dag, cfg); //update child max 100 iterations
				}

			}

			// update parenthood map
			map_parent.clear();
			for(Node node : map_subgraphs.keySet()) {
				// map_parent is updated in function updateParent()
				updateParentMap(node, dag);
			}

			// update the two sets for comparison
			previous_no_parents.clear();
			previous_no_parents.addAll(no_parents);
			no_parents.clear();
			no_parents.addAll(map_subgraphs.keySet());
			no_parents.removeAll(map_parent.keySet());

			count++;
		}
	}
	
	public static Map<Node, List<AtlasSet<Node>>> getMap(){
		return map_subgraphs;
	}

	public static AtlasSet<Node> getSelectable(Q cfg){
		return cfg.nodesTaggedWithAll("STRUCT_SELECTABLE").eval().nodes();
	}
	
	/**
	* Pre-process the whole graph and store the child-parent relationships and subgraphs for each control flow condition node
	 * @param Q function
	 * @return none
	 */
//	public static void preprocess(Q function) {
//		// clear memory for previous functions
//		map_subgraphs.clear();
//		map_parent.clear();
//		
//		// run DLI to tag all loops
//		com.ensoftcorp.open.jimple.commons.loops.DecompiledLoopIdentification.recoverLoops();
//		
//
//		// initialize necessary variables
//		Q cfg = CommonQueries.cfg(function);
//		Q cfbe=cfg.edges(XCSG.ControlFlowBackEdge).retainEdges(); //Control flow back edge
//		Q dag=cfg.differenceEdges(cfbe); // Control flow back edges removed
//		
//		AtlasSet<Node> label_set = cfg.nodesTaggedWithAll("isLabel").eval().nodes();
//		
//		for(Node label : label_set) {
//			if(label.taggedWith(XCSG.Loop)) {
//				continue;
//			}
//			List<AtlasSet<Node>> l = getModule(cfg, label);
//			String s = label.getAttr(XCSG.name).toString() + " | " + l.get(0).size() + ", " + l.get(1).size() + ", " + l.get(2).size();
//			Log.info(s);
//		}
//		
//	}
//	
	// edu.iastate.structured.core.GraphAnalyzer.analyzeAll("file/path/*.txt")
	public static void analyzeAll(String path) throws IOException {
		analyzeAll(new File(path));
	}
	
	public static void analyzeAll(File file) throws IOException {
		// get saving directory
		new GraphAnalyzer().createDirectory();
		// run DLI to tag all loops
//		com.ensoftcorp.open.jimple.commons.loops.DecompiledLoopIdentification.recoverLoops();
		
		//		get all functions with labels
		AtlasSet<Node> function_w_label = Common.universe().nodesTaggedWithAll("isLabel").containers().nodes(XCSG.Function).eval().nodes();
		
		int num = 0;
		FileWriter writer = new FileWriter(file);
		for(Node function: function_w_label) {
			Q cfg = CommonQueries.cfg(Common.toQ(function));
			
			
			map_subgraphs.clear();
			map_parent.clear();
			analyze(cfg);
			
			
			for(Node label : map_subgraphs.keySet()) {
				List<AtlasSet<Node>> l = map_subgraphs.get(label);
				
				if(l.get(0).size() > 1) {
					writer.write(function.getAttr(XCSG.name) + ", " + label.getAttr(XCSG.name) + " || " + l.get(0).size() + "\n");
					// mark up
					Markup markup = new Markup();
					markup.set(Common.toQ(l.get(1)), MarkupProperty.NODE_BACKGROUND_COLOR, Color.YELLOW.darker());
					markup.set(Common.toQ(l.get(2)), MarkupProperty.NODE_BACKGROUND_COLOR, Color.CYAN);
					markup.set(Common.toQ(l.get(0)), MarkupProperty.NODE_BACKGROUND_COLOR, Color.MAGENTA);
					
					// set file name
					String sourceFile = getQualifiedFunctionName(function);
					String methodName =  function.getAttr(XCSG.name).toString();
					
					// output CFG
					saveDisplayCFG(cfg.eval(), num, sourceFile, methodName, markup, false);
					num++;
				}
			}
			
		}
		
		writer.close();
		
	}


}
