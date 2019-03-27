package edu.iastate.labels.core;

import java.util.List;
import java.util.Map;
import java.util.Set;
import java.awt.Color;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

import com.ensoftcorp.atlas.core.db.graph.Graph;
import com.ensoftcorp.atlas.core.db.graph.Node;
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
import com.ensoftcorp.open.pcg.common.PCGFactory;

import edu.iastate.labels.core.VerificationProperties;

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
	 * The name pattern for the directory containing the graphs for the processed goto.
	 * <p>
	 * 1- The {@link SourceCorrespondence}.
	 */
	private static String GOTO_GRAPH_DIRECTORY_NAME_PATTERN = "labelModule_graphs";
	
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
	
	public LabelAnalyzer()
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
		// get saving directory
		new LabelAnalyzer().createDirectory();
		// run DLI to tag all loops
		com.ensoftcorp.open.jimple.commons.loops.DecompiledLoopIdentification.recoverLoops();
		
		//		get all functions with labels
		AtlasSet<Node> function_w_label = Common.universe().nodesTaggedWithAll("isLabel").containers().nodes(XCSG.Function).eval().nodes();
		
		int num = 0;
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
	
	public static void writeGotoFunc() throws IOException {
		// get saving directory
		new LabelAnalyzer().createDirectory();
		
		//		get all functions with labels
		AtlasSet<Node> function_w_label = Common.universe().nodes(XCSG.Project).contained().nodesTaggedWithAll("isLabel").containers().nodes(XCSG.Function).eval().nodes();
		
		int num = 0;
		for(Node function: function_w_label) {
			Q cfg = CommonQueries.cfg(Common.toQ(function));
			
			AtlasSet<Node> label_set = cfg.nodesTaggedWithAll("isLabel").eval().nodes();
			AtlasSet<Node> goto_set = cfg.nodesTaggedWithAll(XCSG.GotoStatement).eval().nodes();
		
			Markup markup = new Markup();
			markup.set(Common.toQ(goto_set), MarkupProperty.NODE_BACKGROUND_COLOR, Color.YELLOW.darker());
			markup.set(Common.toQ(label_set), MarkupProperty.NODE_BACKGROUND_COLOR, Color.MAGENTA);
			
			// set file name
			String sourceFile = getQualifiedFunctionName(function);
			String methodName =  function.getAttr(XCSG.name).toString();
			
			// output CFG
			saveDisplayCFG(cfg.eval(), num, sourceFile, methodName, markup, false);
			num++;
			
			
		}
		
	}
	
	public static void calcGoto() {
		
		AtlasSet<Node> function_w_label = Common.universe().nodes(XCSG.Project).contained().nodesTaggedWithAll("isLabel").containers().nodes(XCSG.Function).eval().nodes();
		
		for(Node function: function_w_label) {
			Q cfg = CommonQueries.cfg(Common.toQ(function));
			AtlasSet<Node> label_set = cfg.nodesTaggedWithAll("isLabel").eval().nodes();
			
			for(Node labelNode : label_set) {
				AtlasSet<Node> predGotoSet = cfg.predecessors(Common.toQ(labelNode)).nodes(XCSG.GotoStatement).eval().nodes();
				labelNode.tag("GotoCount_"+predGotoSet.size());
			}
			
		}
		Log.info("Done With Goto Count");
	}

	public static void calcGoto(String filePath) throws IOException  {
		FileWriter writer = new FileWriter(new File(filePath));
		writer.write("function_name, label_node, goto_count, predecessor_count\n");
		BufferedWriter br = new BufferedWriter(writer);
		
		AtlasSet<Node> function_w_label = Common.universe().nodes(XCSG.Project).contained().nodesTaggedWithAll("isLabel").containers().nodes(XCSG.Function).eval().nodes();
		
		for(Node function: function_w_label) {
			Q cfg = CommonQueries.cfg(Common.toQ(function));
			AtlasSet<Node> label_set = cfg.nodesTaggedWithAll("isLabel").eval().nodes();
			
			String function_name = function.getAttr(XCSG.name).toString();
			
			for(Node labelNode : label_set) {
				AtlasSet<Node> predSet = cfg.predecessors(Common.toQ(labelNode)).eval().nodes();
				AtlasSet<Node> predGotoSet = Common.toQ(predSet).nodes(XCSG.GotoStatement).eval().nodes();
//				labelNode.tag("GotoCount_"+predGotoSet.size());

				br.write(function_name + "," + labelNode.getAttr(XCSG.name).toString() + "," + predGotoSet.size() + "," + predSet.size() + "\n");
				
				br.flush();
			}
			
		}
		writer.close();
		Log.info("Done With Goto Count");
	}
	
	public static void writeLabelPCG() throws IOException {
		GOTO_GRAPH_DIRECTORY_NAME_PATTERN = "writeLabelPCG";
		
		// get saving directory
		new LabelAnalyzer().createDirectory();
		
		//		get all functions with labels
		AtlasSet<Node> function_w_label = Common.universe().nodes(XCSG.Project).contained().nodesTaggedWithAll("isLabel").containers().nodes(XCSG.Function).eval().nodes();
		
		int num = 0;
		for(Node function: function_w_label) {
			num++;
			Q cfg = CommonQueries.cfg(Common.toQ(function));
			
			AtlasSet<Node> label_set = cfg.nodesTaggedWithAll("isLabel").eval().nodes();
			AtlasSet<Node> goto_set = cfg.nodesTaggedWithAll(XCSG.GotoStatement).eval().nodes();
			AtlasSet<Node> return_set = cfg.nodesTaggedWithAll(XCSG.controlFlowExitPoint).eval().nodes();
			
			Markup markup = new Markup();
			markup.set(Common.toQ(label_set), MarkupProperty.NODE_BACKGROUND_COLOR, Color.RED);
			markup.set(Common.toQ(goto_set), MarkupProperty.NODE_BACKGROUND_COLOR, Color.YELLOW);
			markup.set(Common.toQ(return_set), MarkupProperty.NODE_BACKGROUND_COLOR, Color.MAGENTA);
			
			// set file name
			String sourceFile = getQualifiedFunctionName(function);
			String methodName =  function.getAttr(XCSG.name).toString();
			
			// output CFG
			saveDisplayCFG(cfg.eval(), num, sourceFile, methodName, markup, false);
			
			
			// output PCG
			Q nodeOfInterestQ = Common.toQ(label_set).union(Common.toQ(goto_set)).union(Common.toQ(return_set));
			AtlasSet<Node> pcg_seed = cfg.nodes(XCSG.ControlFlowCondition).union(nodeOfInterestQ).eval().nodes();
			
			Q pcg = PCGFactory.create(cfg, Common.toQ(pcg_seed)).getPCG();
			saveDisplayPCG(pcg.eval(), num, sourceFile, methodName, markup, false);
			
			
		}
		
	}
	
	public static void writeLabelStats(String filePath) throws IOException {
		// Write statistics for different categories of labels
			
		// get saving directory
		new LabelAnalyzer().createDirectory();
		
		if(Common.universe().nodes("NATURAL_LOOP").eval().nodes().size()<1) {
			com.ensoftcorp.open.jimple.commons.loops.DecompiledLoopIdentification.recoverLoops();
			Log.info("DLI Done");
		}else {
			Log.info("No need for DLI");
		}
		
		FileWriter writer = new FileWriter(new File(filePath), true);
		writer.write("Function_number, Function_name, Total_labels, Exit_control, Loop_creation, Error_exit, Redundant, Unreachable\n");
		BufferedWriter br = new BufferedWriter(writer);
		
		//		get all functions with labels
		AtlasSet<Node> function_w_label = Common.universe().nodes(XCSG.Project).contained().nodesTaggedWithAll("isLabel").containers().nodes(XCSG.Function).eval().nodes();
		
		int num = 0;
		for(Node function: function_w_label) {
			num++;
			
			int exitCtrl = 0;
			int loopCreate = 0;
			int errorExit = 0;
			int redundant = 0;
			int unreachable = 0;
			
			//CFG/DAG
			Q cfgQ = CommonQueries.cfg(Common.toQ(function));
			Q cfbeQ=cfgQ.edges(XCSG.ControlFlowBackEdge).retainEdges(); //Control flow back edge
			Q dagQ=cfgQ.differenceEdges(cfbeQ); // Control flow back edges removed
			
			AtlasSet<Node> labelSet = cfgQ.nodesTaggedWithAll("isLabel").eval().nodes();
			
			for(Node labelNode : labelSet) {
				AtlasSet<Node> predSet = dagQ.predecessors(Common.toQ(labelNode)).eval().nodes();
				
				//check exception handling
				if(predSet.size()>1 && Common.toQ(labelNode).nodes(XCSG.Loop).eval().nodes().size()==0) {
					exitCtrl++;
				}
				
				//check loop creation
				if(Common.toQ(labelNode).nodes(XCSG.Loop).eval().nodes().size()>0) {
					loopCreate ++;
				}
				
				//check error exit
				
				/////get map for loop children				
				AtlasSet <Node> loopNodeSet = cfgQ.nodes(XCSG.Loop).eval().nodes();
				
				int count = 0;
				
				for(Node loopEntryNode : loopNodeSet) {
					AtlasSet <Node> loopChildGotoNodeSet = Common.universe().edges(XCSG.LoopChild).
			        		forward(Common.toQ(loopEntryNode)).retainNodes().nodes(XCSG.GotoStatement).eval().nodes();
					if(Common.toQ(loopChildGotoNodeSet).intersection(dagQ.predecessors(Common.toQ(labelNode))).eval().nodes().size()>0) {
						count ++;
					}
				}
				
				if(count > 1) {
					errorExit ++;
				}
				
				//check redundant
				AtlasSet<Node> labelBodySet = dagQ.forward(Common.toQ(labelNode)).difference(Common.toQ(labelNode)).eval().nodes();
				if(predSet.size()==1 && dagQ.predecessors(Common.toQ(labelBodySet)).eval().nodes().size()<2) {
					redundant ++;
				}
				
				//check unreachable
				if(predSet.size() == 0) {
					unreachable++;
				}
			}
			br.write(num + "," + function.getAttr(XCSG.name).toString() + "," + labelSet.size() + "," + exitCtrl + "," + loopCreate + "," + errorExit + "," + redundant + "," + unreachable + "\n");
			br.flush();	
			
		}
		writer.close();
	}
	
	public static void writeBasicStats(String filePath) throws IOException {
		// Write statistics for different categories of labels
			
		// get saving directory
		new LabelAnalyzer().createDirectory();
		
		if(Common.universe().nodes("NATURAL_LOOP").eval().nodes().size()<1) {
			com.ensoftcorp.open.jimple.commons.loops.DecompiledLoopIdentification.recoverLoops();
			Log.info("DLI Done");
		}else {
			Log.info("No need for DLI");
		}
		
		FileWriter writer = new FileWriter(new File(filePath), true);
		writer.write("Function_number, Function_name, nodes_CFG, edges_CFG, gotos, labels, CtrlBlks, nodes_PCG, edges_PCG\n");
		BufferedWriter br = new BufferedWriter(writer);
		
		//		get all functions with labels
		AtlasSet<Node> function_w_label = Common.universe().nodes(XCSG.Project).contained().nodesTaggedWithAll("isLabel").containers().nodes(XCSG.Function).eval().nodes();
		
		int num = 0;
		for(Node function: function_w_label) {
			num++;
			
			//CFG/DAG
			Q cfgQ = CommonQueries.cfg(Common.toQ(function));
//			Q cfbeQ=cfgQ.edges(XCSG.ControlFlowBackEdge).retainEdges(); //Control flow back edge
//			Q dagQ=cfgQ.differenceEdges(cfbeQ); // Control flow back edges removed
			
			//PCG
			AtlasSet<Node> label_set = cfgQ.nodes("isLabel").eval().nodes();
			AtlasSet<Node> goto_set = cfgQ.nodes(XCSG.GotoStatement).eval().nodes();
			AtlasSet<Node> return_set = cfgQ.nodes(XCSG.controlFlowExitPoint).eval().nodes();
			
			Q nodeOfInterestQ = Common.toQ(label_set).union(Common.toQ(goto_set)).union(Common.toQ(return_set));
			AtlasSet<Node> pcg_seed = cfgQ.nodes(XCSG.ControlFlowCondition).union(nodeOfInterestQ).eval().nodes();
			Q pcgQ = PCGFactory.create(cfgQ, Common.toQ(pcg_seed)).getPCG();
			
			AtlasSet<Node> gotoSet = cfgQ.nodes(XCSG.GotoStatement).eval().nodes();
			AtlasSet<Node> labelSet = cfgQ.nodes("isLabel").eval().nodes();
			AtlasSet<Node> cbEntrySet = cfgQ.nodesTaggedWithAny(XCSG.ControlFlowCondition, XCSG.Loop).eval().nodes();
			
			long nodes_CFG = cfgQ.eval().nodes().size();
			long edges_CFG = cfgQ.eval().edges().size();
			long gotos = gotoSet.size();
			long labels = labelSet.size();
			long CtrlBlks = cbEntrySet.size();
			long nodes_PCG = pcgQ.eval().nodes().size();
			long edges_PCG = pcgQ.eval().edges().size();
			
			
			br.write(num + "," + function.getAttr(XCSG.name).toString() + "," + nodes_CFG + "," + edges_CFG + "," + gotos + "," + labels + "," + CtrlBlks + "," + nodes_PCG + "," + edges_PCG + "\n");
			br.flush();	
			
		}
		writer.close();
	}

}
