package edu.iastate.labels.core;

import java.util.List;
import java.util.Map;
import java.util.Set;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

import com.ensoftcorp.atlas.core.db.graph.Node;
import com.ensoftcorp.atlas.core.db.set.AtlasHashSet;
import com.ensoftcorp.atlas.core.db.set.AtlasSet;
import com.ensoftcorp.atlas.core.query.Q;
import com.ensoftcorp.atlas.core.script.Common;
import com.ensoftcorp.atlas.core.script.CommonQueries;
import com.ensoftcorp.atlas.core.xcsg.XCSG;

import edu.iastate.labels.viewer.log.Log;

/**
* This program checks if a given function or all functions in mapped workspace are structured
* It parses through all the control flow condition nodes and obtain the subgraph under them
* If the subgraph has more than one entries, it is unstructured.
*
* @author Le Zhang
*/
public class LabelAnalyzer {
	private static Map<Node, List<AtlasSet<Node>>> map_subgraphs = new HashMap<Node, List<AtlasSet<Node>>>(); // format: <Node controlFlowCondition, List<Q entry, Q body, Q exit> >
	private static Map<Node, Node> map_parent = new HashMap<Node, Node>(); // format: <ChildNode, ParentNode>

	/**
	 * Given a file, create a CSV with names of all functions and whether or not
	 * it is structured within the function
	 *
	 * Example Atlas Shell Usage:
	 * edu.iastate.scode.sCodeChecker.parseAllFunctions("C:\Users\TA\Desktop\structured-list.csv")
	 *
	 * @param String path
	 * @throws IOException
	 */
	public static void parseAllFunctions(String path) throws IOException {
		parseAllFunctions(new File(path));
	}

	/**
	 * Given a file, create a CSV with names of all functions and whether or not
	 * it is structured within the function
	 *
	 * Example Atlas Shell Usage:
	 * edu.iastate.scode.sCodeChecker.parseAllFunctions(new java.io.File("C:\Users\TA\Desktop\structured-list.csv"))
	 *
	 * @param File filepath
	 * @throws IOException
	 */
	public static void parseAllFunctions(File file) throws IOException {
		FileWriter writer = new FileWriter(file);
		Q functions = Common.universe().nodesTaggedWithAny(XCSG.Function);
		for(Node function: functions.eval().nodes()) {
			Log.info("Processing " + function.getAttr(XCSG.name));

			// parse the function
			boolean result = fun_isStructured(Common.toQ(function));

			writer.write(function.getAttr(XCSG.name) + "," + (result? "true":"false") + "\n");
			Log.info("Done with " + function.getAttr(XCSG.name));
		}
		// add Excel False counter in the last line
		long count = functions.eval().nodes().size();
		String formula = "=COUNTIF(B1:B" + count + ", \"\"FALSE\"\")";
		writer.write(",\""+ formula +"\"\n");
		writer.close();
	}

	/**
	* Checks if a given function is structured
	*
	 * @param Q function
	 * @return boolean
	 */
	public static boolean fun_isStructured(Q function) {
		preprocess(function);
		return parse();

	}

	/**
	* Checks if a given function is structured
	*
	 * Example Atlas Shell Usage:
	 * edu.iastate.scode.sCodeChecker.fun_isStructured("function_name")
	 *
	 * @param String fun
	 * @return boolean
	 */
	public static boolean fun_isStructured(String fun) {
		Q function = com.ensoftcorp.open.c.commons.analysis.CommonQueries.functions(fun);
		preprocess(function);
		return parse();

	}

	/**
	* Goes through all the subgraphs to see if there are two entries in one subgraph
	 * @param none
	 * @return boolean
	 */
	public static boolean parse() {

		for(Node current : map_subgraphs.keySet()) {
			if(map_subgraphs.get(current).get(0).size()>1) {
				// if more than one entry to a subgraph, return false
				return false;
			}
		}
		return true;
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
		
		AtlasSet<Node> body = new AtlasHashSet<Node>();
		AtlasSet<Node> exit = new AtlasHashSet<Node>();
		if(label_nodes.eval().nodes().size() > 1) {
			Q sub_label_graph = dag_no_break.forward(label_nodes.difference(Common.toQ(label)));
			subgraph = subgraph.difference(sub_label_graph).union(sub_label_graph.roots()).induce(dag_no_break).retainEdges();	
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

	/**
	* Pre-process the whole graph and store the child-parent relationships and subgraphs for each control flow condition node
	 * @param Q function
	 * @return none
	 */
	public static void preprocess(Q function) {
		// clear memory for previous functions
		map_subgraphs.clear();
		map_parent.clear();
		
		// run DLI to tag all loops
		com.ensoftcorp.open.jimple.commons.loops.DecompiledLoopIdentification.recoverLoops();
		

		// initialize necessary variables
		Q cfg = CommonQueries.cfg(function);
		Q cfbe=cfg.edges(XCSG.ControlFlowBackEdge).retainEdges(); //Control flow back edge
		Q dag=cfg.differenceEdges(cfbe); // Control flow back edges removed
		
		AtlasSet<Node> label_set = cfg.nodesTaggedWithAll("isLabel").eval().nodes();
		
		for(Node label : label_set) {
			if(label.taggedWith(XCSG.Loop)) {
				continue;
			}
			List<AtlasSet<Node>> l = getModule(cfg, label);
			String s = label.getAttr(XCSG.name).toString() + " | " + l.get(0).size() + ", " + l.get(1).size() + ", " + l.get(2).size();
			Log.info(s);
		}
		
	}
	
	// edu.iastate.labels.core.LabelAnalyzer.analyzeAll("file/path/*.txt")
	public static void analyzeAll(String path) throws IOException {
		analyzeAll(new File(path));
	}
	
	public static void analyzeAll(File file) throws IOException {
		// run DLI to tag all loops
		com.ensoftcorp.open.jimple.commons.loops.DecompiledLoopIdentification.recoverLoops();
		
		//		get all functions with labels
		AtlasSet<Node> function_w_label = Common.universe().nodesTaggedWithAll("isLabel").containers().nodes(XCSG.Function).eval().nodes();
		
		
		FileWriter writer = new FileWriter(file);
		List<AtlasSet<Node>> l = new ArrayList<AtlasSet<Node>>();
		for(Node function: function_w_label) {
			Q cfg = CommonQueries.cfg(Common.toQ(function));
			
			AtlasSet<Node> label_set = cfg.nodesTaggedWithAll("isLabel").eval().nodes();
			
			for(Node label : label_set) {
				if(label.taggedWith(XCSG.Loop)) {
					continue;
				}
				l = getModule(CommonQueries.cfg(Common.toQ(function)), label);
				
				if(l.get(0).size() > 1) {
					writer.write(function.getAttr(XCSG.name) + ", " + label.getAttr(XCSG.name) + " || " + l.get(0).size() + "\n");
				}
			}
			
			
			
		}
		
		writer.close();
		
	}


}
