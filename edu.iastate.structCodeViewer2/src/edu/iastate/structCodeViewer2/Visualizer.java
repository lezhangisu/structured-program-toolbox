package edu.iastate.structCodeViewer2;

import java.awt.Color;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import com.ensoftcorp.atlas.core.db.graph.Node;
import com.ensoftcorp.atlas.core.db.set.AtlasHashSet;
import com.ensoftcorp.atlas.core.db.set.AtlasSet;
import com.ensoftcorp.atlas.core.markup.Markup;
import com.ensoftcorp.atlas.core.markup.MarkupProperty;
import com.ensoftcorp.atlas.core.query.Q;
import com.ensoftcorp.atlas.core.script.Common;
import com.ensoftcorp.atlas.core.script.StyledResult;
import com.ensoftcorp.atlas.core.xcsg.XCSG;
import com.ensoftcorp.atlas.ui.scripts.selections.FilteringAtlasSmartViewScript;
import com.ensoftcorp.atlas.ui.selection.event.IAtlasSelectionEvent;
import com.ensoftcorp.open.c.commons.analysis.CommonQueries;


import edu.iastate.structCodeViewer2.log.Log;

/**
 * For a selected function, displays the control flow graph. The edge back to
 * the start of the loop is highlighted in blue.
 */
public class Visualizer extends FilteringAtlasSmartViewScript {
	private Map<Node, List<AtlasSet<Node>>> map_subgraphs = new HashMap<Node, List<AtlasSet<Node>>>(); // format: <Node controlFlowCondition, List<Q entry, Q body, Q exit> >
	private Map<Node, Node> map_parent = new HashMap<Node, Node>(); // format: <ChildNode, ParentNode>
	private Node previous_function = null;

	@Override
	public String[] getSupportedNodeTags() { // Event Trigger
		return new String[]{XCSG.Function, XCSG.ControlFlow_Node};
	}

	@Override
	public String[] getSupportedEdgeTags() {
		return FilteringAtlasSmartViewScript.NOTHING; // Don't response to clicks on edges
	}

	@Override
	public StyledResult selectionChanged(IAtlasSelectionEvent input, Q filteredSelection) {

		Q function = filteredSelection.nodes(XCSG.Function);
		Q cf_node = filteredSelection.nodes(XCSG.ControlFlow_Node);
		Q cf_condition = filteredSelection.nodes(XCSG.ControlFlowCondition);
		Q f = Common.empty();
		Q cfg = Common.empty();

		if(!function.eval().nodes().isEmpty()) {
			// if no function, return original graph
			Log.info("Function " + function.eval().nodes().one().getAttr(XCSG.name) + " Selected");
			cfg = CommonQueries.cfg(function);

			// pre-process the graph
			if(previous_function!=null && function.eval().nodes().one().equals(previous_function)) {
				Log.info("Preprocess Already Done");
			}else {
				preprocess(function);
			}
			previous_function = function.eval().nodes().one();

			Markup m = new Markup();
			m.setEdge(Common.codemap().edges(XCSG.ControlFlowBackEdge), MarkupProperty.EDGE_COLOR, Color.BLUE);

			return new StyledResult(cfg, m);

		}else if(!cf_condition.eval().nodes().isEmpty()) {
			Log.info("Control Flow Condition Node \" " + cf_condition.eval().nodes().one().getAttr(XCSG.name) + "\" Selected");

			// if selected a control flow node, parse for subgraph
			function = cf_condition.parent().nodes(XCSG.Function); // find the parent function
			cfg = CommonQueries.cfg(function); // get cfg from the function

			// pre-process the graph
			if(previous_function!=null && function.eval().nodes().one().equals(previous_function)) {
				Log.info("Preprocess Already Done");
			}else {
				preprocess(function);
			}
			previous_function = function.eval().nodes().one();

			// list [entry, subgraph, exits]
			List<AtlasSet<Node>> subgraph = map_subgraphs.get(cf_condition.eval().nodes().one());

			// log subgraph info
			Log.info("Subgraph size: " + (subgraph.get(1).size()+subgraph.get(0).size()+subgraph.get(2).size()));
			Log.info("Body size: " + subgraph.get(1).size());
			Log.info("Entry size: " + subgraph.get(0).size());
			Log.info("Exit size: " + subgraph.get(2).size());

			// init the markup
			Markup m = new Markup();
			if(subgraph.size() >= 3) {
				// mark nodes and edges within this subgraph with yellow color
				m.setNode(Common.toQ(subgraph.get(1)), MarkupProperty.NODE_BACKGROUND_COLOR, Color.YELLOW);
				// mark exits with Cyan color
				m.setNode(Common.toQ(subgraph.get(2)), MarkupProperty.NODE_BACKGROUND_COLOR, Color.CYAN);
				// mark entry nodes with Magenta
				m.setNode(Common.toQ(subgraph.get(0)), MarkupProperty.NODE_BACKGROUND_COLOR, Color.MAGENTA);
				// mark control flow back edge with blue
				m.setEdge(Common.codemap().edges(XCSG.ControlFlowBackEdge), MarkupProperty.EDGE_COLOR, Color.BLUE);
				// mark subgraph edges with red
				m.setEdge(Common.toQ(subgraph.get(1)).union(Common.toQ(subgraph.get(0))).union(Common.toQ(subgraph.get(2))).induce(cfg.retainEdges()), MarkupProperty.EDGE_COLOR, Color.RED);
			}
			return new StyledResult(cfg, m);

		}else if(!cf_node.eval().nodes().isEmpty()) {
			Log.info("Ordinary Control Flow Node Selected");

			f = cf_node.parent().nodes(XCSG.Function); // find the parent function
			cfg = CommonQueries.cfg(f); // get cfg from the function

			Markup m = new Markup();
			m.setEdge(Common.codemap().edges(XCSG.ControlFlowBackEdge), MarkupProperty.EDGE_COLOR, Color.BLUE);

			return new StyledResult(cfg, m);
		}
		return null;

	}

	/**
	* Pre-process the whole graph and store the nesting relationships and subgraphs for each legal entry points
	 * @param cfg
	 * @return none
	 */
	private void preprocess(Q function) {
		// clear memory for previous functions
		map_subgraphs.clear();
		map_parent.clear();

		// initialize necessary variables
		Q cfg = CommonQueries.cfg(function);
		Q cfbe=cfg.edges(XCSG.ControlFlowBackEdge).retainEdges(); //Control flow back edge
		Q dag=cfg.differenceEdges(cfbe); // Control flow back edges removed

//		Map<Node, Long> subgraph_size = new HashMap<Node, Long>();
//		List<Node> sorted_by_size = new ArrayList<Node>();

		// initiate all the initial subgraphs
		for(Node node : cfg.nodesTaggedWithAny(XCSG.ControlFlowCondition).eval().nodes()) {
			// get subgraph information
			List<AtlasSet<Node>> list = getSubgraph(Common.toQ(node), cfg);
			// update subgraph list
			map_subgraphs.put(node, list);
			// update parenthood map
			updateParent(node, dag);

			// get subgraph size
//			subgraph_size.put(node, list.get(0).size()+list.get(1).size());

			// initialize sort by size list
//			sorted_by_size.add(node);
		}

		// update subgraphs based on parents' exits
		// start with nodes with no parents
		Set<Node> no_parents = new HashSet<Node>();
		Set<Node> previous_no_parents = new HashSet<Node>();
		no_parents.addAll(map_subgraphs.keySet());
		no_parents.removeAll(map_parent.keySet());

		// update all nested subgraphs
		// while set of no parent subgraphs changes
		int count = 0;
		while(!(previous_no_parents.size() == no_parents.size() && previous_no_parents.containsAll(no_parents))) {
			// for each subgraph with no parent
			for(Node node : no_parents) {
				// get children
				AtlasSet<Node> children = new AtlasHashSet<Node>();
				children.addAll(Common.toQ(map_subgraphs.get(node).get(1)).nodesTaggedWithAny(XCSG.ControlFlowCondition).eval().nodes());

				// if no child, skip
				if(children.size() < 1) {
					continue;
				}

				// update child subgraph
				for(Node child : children) {
					updateExits(100, child, dag, cfg);
				}

			}

			// update parenthood map
			map_parent.clear();
			for(Node node : map_subgraphs.keySet()) {
				// map_parent is updated in function updateParent()
				updateParent(node, dag);
			}

			// update the two sets for comparison
			previous_no_parents.clear();
			previous_no_parents.addAll(no_parents);
			no_parents.clear();
			no_parents.addAll(map_subgraphs.keySet());
			no_parents.removeAll(map_parent.keySet());

			count++;
			if(count>100) {
				Log.info("Update child subgraph exceeds max iterations for FUNCTION: " + function.eval().nodes().one().getAttr(XCSG.name));
				break;
			}
		}

		Log.info("Pre-processing DONE");

//		for(Node node : map_parent.keySet()) {
//			Log.info(node.getAttr(XCSG.name) + " |:| " + map_parent.get(node).getAttr(XCSG.name));
//		}
	}

	/**
	* Update parent map of all children in its subgarph
	 * @param Parent Node
	 * @return None
	 */
	private void updateParent(Node parent_node, Q dag) {  // input: graph root and graph list [entry, body, exit]

		List<AtlasSet<Node>> parent_graph = map_subgraphs.get(parent_node);
		Q parent_graph_body_q = Common.toQ(parent_graph.get(1));

		// update exits of nested nodes
		for(Node child : parent_graph_body_q.nodesTaggedWithAny(XCSG.ControlFlowCondition).eval().nodes()) {
			if(map_parent.containsKey(child)) {
				Node prev_parent = map_parent.get(child);
				// compare previous parent with current parent
				// pick the smaller sized father to be the actual parent
//				Log.info(parent_node.getAttr(XCSG.name).toString() + " =new=> " + child.getAttr(XCSG.name).toString() + " = " + distance(parent_node, child, dag));
//				Log.info(prev_parent.getAttr(XCSG.name).toString() + " =old=> " + child.getAttr(XCSG.name).toString() + " = " + distance(prev_parent, child, dag));
//				if(dag.between(Common.toQ(parent_node), Common.toQ(child)).eval().nodes().size()
//						< dag.between(Common.toQ(prev_parent), Common.toQ(child)).eval().nodes().size()) {
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
	private int getDistance(Node node1, Node node2, Q dag) {
		AtlasSet<Node> current = new AtlasHashSet<Node>();
		current.add(node1);
		int steps = 0;
		if(dag.forward(Common.toQ(node1)).eval().nodes().contains(node2)) {
			int count = 0;
			while(!current.isEmpty()) {
				steps += 1;
				AtlasSet<Node> tmp = new AtlasHashSet<Node>();
				for(Node node : current) {
					AtlasSet<Node> tmp_nxt = dag.successors(Common.toQ(node)).eval().nodes();
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
	* Update the parent exit info for children subgraphs
	 * @param child node, its subgraph
	 * @return none
	 */
	private void updateExits(int loop, Node current, Q dag, Q cfg) {
		//avoid deadlock
		if(loop == 0) {
			Log.info("updateExits() exceeds max recursion");
			return;
		}

		// cast to Q
		Q cf_condition = Common.toQ(current);

		// list [entry, subgraph, exits]
		List<AtlasSet<Node>> subgraph = map_subgraphs.get(current);

		// terminate subgraph based on exits of parent subgraph
		// if it has a parent
		if(map_parent.containsKey(current)) {

			// get parent exits
			AtlasSet<Node> parent_exits = map_subgraphs.get(map_parent.get(current)).get(2);
			// get paths starting from parent's exits
			Q extra_portion = dag.forward(Common.toQ(parent_exits)).retainEdges();

			// get subgraph body nodes
			// need to include entries because at this point some body nodes may be treated as entries
			Q subgraph_body_q = Common.toQ(subgraph.get(1)).union(Common.toQ(subgraph.get(0)));

			// if there is an intersection
			if(extra_portion.intersection(subgraph_body_q).eval().nodes().size() > 0) {

				//==============debugging === 05-03-2018
//				Log.info("======UpdateExit====== "+current.getAttr(XCSG.name).toString());
//				Log.info("===Before===");
//				String str="";
//				for(Node n : subgraph.get(2)) {
//					str+=n.getAttr(XCSG.name).toString()+" || ";
//				}
//				Log.info(str);
				//=============== === 05-03-2018

				// update the subgraph body
				AtlasSet<Node> temp = new AtlasHashSet<Node>();

				temp.addAll(subgraph.get(1));
				temp = Common.toQ(temp).difference(extra_portion).eval().nodes();

				subgraph.set(1, temp);

				// update exits
				AtlasSet<Node> temp2 = Common.toQ(subgraph.get(1)).union(cf_condition).union(Common.toQ(parent_exits)).induce(cfg).retainEdges().leaves().eval().nodes();

				subgraph.set(2, temp2);

				// update the entries
				AtlasSet<Node> temp3 = new AtlasHashSet<Node>();
				// pick up entry nodes
				AtlasSet<Node> subgraph_body_set = Common.toQ(subgraph.get(1)).union(cf_condition).eval().nodes();
				for(Node n : subgraph_body_set) {
					for(Node ent : cfg.predecessors(Common.toQ(n)).eval().nodes()) {
						if(!subgraph_body_set.contains(ent)) {
							temp3.add(n);
						}
					}
				}
				subgraph.set(0, temp3);

				// update new subgraph
				map_subgraphs.put(current, subgraph);

				//=============== debugging === 05-03-2018
//				Log.info("===After===");
//				str="";
//				for(Node n : subgraph.get(2)) {
//					str+=n.getAttr(XCSG.name).toString()+" || ";
//				}
//				Log.info(str);

				// update its children === 05-03-2018
				AtlasSet<Node> its_children = Common.toQ(subgraph.get(1)).nodesTaggedWithAny(XCSG.ControlFlowCondition).eval().nodes();
				if(its_children.size()>0) {
					for(Node forward_child : its_children) {
						Log.info("Parent:: " + current.getAttr(XCSG.name) + " ||Child:: " + forward_child.getAttr(XCSG.name));
						updateExits(loop--, forward_child, dag, cfg);
					}
				}
				//================
			}
		}
	}

	/**
	* returns a list of the subgraph [entry_set, body_set, exit_set]
	 * @param cf_nodes
	 * @return List<Q>
	 */
	private List<AtlasSet<Node>> getSubgraph(Q cf_condition, Q cfg) {

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

			// get the subgraph
			subgraph_q =
					// get the part from loop condition to DAG leaves (to include the loop and return statements)
					dag.between(cf_condition, dag.leaves()).
					// get the part from loop condition to false node (to include possible break statements)
					union(dag.between(cf_condition, falseNode)).
					// exclude the part from false node to DAG leaves
					difference(dag.between(falseNode, dag.leaves()).retainEdges()).
					// put back false node and false edge to make the subgraph complete
					union(falseNode).union(falseEdge).retainEdges();


			// use induce(cfg) to add missing edges from CFG so we have complete subgraph
			subgraph_q = subgraph_q.induce(cfg).retainEdges();

			// get exit nodes
			subgraph_exit_q = subgraph_q.leaves();

			// get legal entry nodes
			subgraph_entry_q = cf_condition;

//**** Long Query Issue Start ***
//			// pick up other illegal entry nodes
//			for(Node n : subgraph_q.difference(subgraph_exit_q).eval().nodes()) {
//				for(Node ent : cfg.predecessors(Common.toQ(n)).eval().nodes()) {
//					if(!subgraph_q.eval().nodes().contains(ent)) {
//						subgraph_entry_q = subgraph_entry_q.union(Common.toQ(n));
//					}
//				}
//			}
//**** Long Query Issue End ***

// FIX ===
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
// FIX END ===

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

//**** Long Query Issue Start ***
			// For every two branch paths, find if there is an intersection
			// save the common intersection to this query
//			Q joint_paths = null;
//
//			for(int i = 0; i<list_paths.size()-1; i++) {
//				for(int j = i+1; j<list_paths.size(); j++) {
//					// get intersections of two branches
//					Q tmp_joint_paths = list_paths.get(i).intersection(list_paths.get(j));
//					if(tmp_joint_paths.eval().nodes().size()>0) {
//						 //if it has an intersection, join it with previous ones
//						if(joint_paths == null) {
//							joint_paths = tmp_joint_paths; // if first intersection found, initialize it
//						}else {
//							joint_paths = joint_paths.intersection(tmp_joint_paths);
//						}
//					}
//				}
//			}
//**** Long Query Issue End

//FIX ===
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
//FIX END ===

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

//**** Long Query Issue Start ***
//			// avoid case-fall-through error situations (no break statement in a case)
//			for(Node exit_node : subgraph_exit_q.nodesTaggedWithAny(XCSG.CaseLabel).eval().nodes()) {
//				// we get the intersection of paths from caseLabeled exit_node to DAG leaves
//				// and from other exit nodes to DAG leaves
//				Q tmp_path = dag.between(Common.toQ(exit_node), dag.leaves()).
//						intersection(dag.between(subgraph_exit_q.difference(subgraph_exit_q.nodesTaggedWithAny(XCSG.CaseLabel)), dag.leaves()));
//				subgraph_q = subgraph_q.union(dag.between(Common.toQ(exit_node), tmp_path.roots()));
//			}
//**** Long Query Issue End

// FIX ===
			if(subgraph_exit_q.nodesTaggedWithAny(XCSG.CaseLabel).eval().nodes().size()>0) {
				Q case2leave = dag.between(subgraph_exit_q.nodesTaggedWithAny(XCSG.CaseLabel), dag.leaves());
				Q nonCase2leave = dag.between(subgraph_exit_q.difference(subgraph_exit_q.nodesTaggedWithAny(XCSG.CaseLabel)), dag.leaves());
				Q case_noncase_intersection = case2leave.intersection(nonCase2leave);
				subgraph_q = dag.between(cf_condition, dag.leaves()).difference(dag.between(case_noncase_intersection.roots(), dag.leaves()))
						.union(case_noncase_intersection.roots());
			}
// FIX END ===


			// complete the subgraph with edges again
			subgraph_q = subgraph_q.union(cf_condition).induce(cfg).retainEdges();

			// update subgraph exits
			subgraph_exit_q = subgraph_q.leaves();

			// get legal entry nodes
			subgraph_entry_q = cf_condition;

//**** Long Query Issue Start ***
//			// pick up other illegal entry nodes
//			for(Node n : subgraph_q.difference(subgraph_exit_q).eval().nodes()) {
//				for(Node ent : cfg.predecessors(Common.toQ(n)).eval().nodes()) {
//					if(!subgraph_q.eval().nodes().contains(ent)) {
//						subgraph_entry_q = subgraph_entry_q.union(Common.toQ(n));
//					}
//				}
//			}
//**** Long Query Issue End ***

// FIX ===
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
//FIX END ===

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

//**** Long Query Issue Start ***
					// pick up other illegal entry nodes

//					for(Node n : subgraph_q.difference(subgraph_exit_q).eval().nodes()) {
//						for(Node ent : cfg.predecessors(Common.toQ(n)).eval().nodes()) {
//							if(!subgraph_q.eval().nodes().contains(ent)) {
//								subgraph_entry_q = subgraph_entry_q.union(Common.toQ(n));
//							}
//						}
//					}
//**** Long Query Issue End ***

// === FIX ===
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
// === FIX END ===
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


	@Override
	public String getTitle() {
		return "Structured Code View 2";
	}
}
