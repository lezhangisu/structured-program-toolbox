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
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;

import com.ensoftcorp.atlas.core.db.graph.Graph;
import com.ensoftcorp.atlas.core.db.graph.Node;
import com.ensoftcorp.atlas.core.db.list.AtlasArrayList;
import com.ensoftcorp.atlas.core.db.list.AtlasList;
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
		AtlasSet<Node> function_w_label = Common.universe().nodesTaggedWithAll("isLabel").parent().nodes(XCSG.Function).eval().nodes();
		
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
		AtlasSet<Node> function_w_label = Common.universe().nodesTaggedWithAll("isLabel").parent().nodes(XCSG.Function).eval().nodes();
		
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
		
		AtlasSet<Node> function_w_label = Common.universe().nodesTaggedWithAll("isLabel").parent().nodes(XCSG.Function).eval().nodes();
		
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
		
		AtlasSet<Node> function_w_label = Common.universe().nodesTaggedWithAll("isLabel").parent().nodes(XCSG.Function).eval().nodes();
		
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
		AtlasSet<Node> labelFunctionSet = Common.universe().nodesTaggedWithAll("isLabel").parent().nodes(XCSG.Function).eval().nodes();

		// make a list so we can sort it
		List<Node> labelFunctionList = new ArrayList<Node>();
		
		for(Node function: labelFunctionSet) {
			labelFunctionList.add(function);
		}
		
		// custom sort
		Collections.sort(labelFunctionList,new Comparator<Node>() {
            @Override
            public int compare(Node n1, Node n2) {
            	// sort with name first, then number of nodes, then edges
                int value1 = n1.getAttr(XCSG.name).toString().compareTo(n2.getAttr(XCSG.name).toString());
                if (value1 == 0) {
                	Q cfgQ1 = CommonQueries.cfg(Common.toQ(n1));
                	Q cfgQ2 = CommonQueries.cfg(Common.toQ(n2));
                	int i1 = (int) cfgQ1.eval().nodes().size();
                	int i2 = (int) cfgQ2.eval().nodes().size();
                    int value2 = i2 - i1;
                    if (value2 == 0) {
                    	int i11 = (int) cfgQ1.eval().edges().size();
                    	int i22 = (int) cfgQ2.eval().edges().size();
                        return i22 - i11;
                    } else {
                        return value2;
                    }
                }
                return value1;
            }
        });
		
		int num = 0;
		for(Node function: labelFunctionList) {
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
			AtlasSet<Node> pcg_seed = nodeOfInterestQ.eval().nodes(); //just interested in label and goto and return nodes
			
			Q pcg = PCGFactory.create(cfg, Common.toQ(pcg_seed)).getPCG();
			saveDisplayPCG(pcg.eval(), num, sourceFile, methodName, markup, false);

		}
		
	}
	
	public static void writeAllCFG() throws IOException {
		GOTO_GRAPH_DIRECTORY_NAME_PATTERN = "writeAllCFG";
		
		// get saving directory
		new LabelAnalyzer().createDirectory();
		
		//		get all functions with labels
		AtlasSet<Node> functionSet = Common.universe().nodes(XCSG.Function).eval().nodes();
		
		// make a list so we can sort it
		List<Node> functionList = new ArrayList<Node>();
		
		for(Node function: functionSet) {
			functionList.add(function);
		}
		
		// custom sort
		Collections.sort(functionList,new Comparator<Node>() {
            @Override
            public int compare(Node n1, Node n2) {
            	// sort with name first, then number of nodes, then edges
                int value1 = n1.getAttr(XCSG.name).toString().compareTo(n2.getAttr(XCSG.name).toString());
                if (value1 == 0) {
                	Q cfgQ1 = CommonQueries.cfg(Common.toQ(n1));
                	Q cfgQ2 = CommonQueries.cfg(Common.toQ(n2));
                	int i1 = (int) cfgQ1.eval().nodes().size();
                	int i2 = (int) cfgQ2.eval().nodes().size();
                    int value2 = i2 - i1;
                    if (value2 == 0) {
                    	int i11 = (int) cfgQ1.eval().edges().size();
                    	int i22 = (int) cfgQ2.eval().edges().size();
                        return i22 - i11;
                    } else {
                        return value2;
                    }
                }
                return value1;
            }
        });
		
		int num = 0;
		for(Node function: functionList) {
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
//			Q nodeOfInterestQ = Common.toQ(label_set).union(Common.toQ(goto_set)).union(Common.toQ(return_set));
//			AtlasSet<Node> pcg_seed = cfg.nodes(XCSG.ControlFlowCondition).union(nodeOfInterestQ).eval().nodes();
//			
//			Q pcg = PCGFactory.create(cfg, Common.toQ(pcg_seed)).getPCG();
//			saveDisplayPCG(pcg.eval(), num, sourceFile, methodName, markup, false);
			
			
		}
		
	}
	
//	public static void writeLabelStats_old(String filePath) throws IOException {
//		// Write statistics for different categories of labels
//			
//		// get saving directory
//		new LabelAnalyzer().createDirectory();
//		
//		if(Common.universe().nodes("NATURAL_LOOP").eval().nodes().size()<1) {
//			com.ensoftcorp.open.jimple.commons.loops.DecompiledLoopIdentification.recoverLoops();
//			Log.info("DLI Done");
//		}else {
//			Log.info("No need for DLI");
//		}
//		
//		FileWriter writer = new FileWriter(new File(filePath), true);
//		writer.write("Function_number, Function_name, Total_labels, Exit_control, Loop_creation, Error_exit, Redundant, Unreachable\n");
//		BufferedWriter br = new BufferedWriter(writer);
//		
//		//		get all functions with labels
//		AtlasSet<Node> function_w_label = Common.universe().nodesTaggedWithAll("isLabel").parent().nodes(XCSG.Function).eval().nodes();
//		
//		int num = 0;
//		for(Node function: function_w_label) {
//			num++;
//			
//			int exitCtrl = 0;
//			int loopCreate = 0;
//			int errorExit = 0;
//			int redundant = 0;
//			int unreachable = 0;
//			
//			//CFG/DAG
//			Q cfgQ = CommonQueries.cfg(Common.toQ(function));
//			Q cfbeQ=cfgQ.edges(XCSG.ControlFlowBackEdge).retainEdges(); //Control flow back edge
//			Q dagQ=cfgQ.differenceEdges(cfbeQ); // Control flow back edges removed
//			
//			//get map for loop children				
//			AtlasSet <Node> loopNodeSet = cfgQ.nodes(XCSG.Loop).eval().nodes();
////			Map<Node, AtlasSet<Node>> loopChildMap = new HashMap<Node, AtlasSet<Node>>();
//						
////			for(Node loopEntryNode : loopNodeSet) {
//				AtlasSet <Node> loopChildNodeSet = Common.universe().edges(XCSG.LoopChild).
//		        		forward(Common.toQ(loopNodeSet)).retainNodes().eval().nodes();
////				loopChildMap.put(loopEntryNode, loopChildGotoNodeSet);
////			}
//			
//			//go through all labels
//			AtlasSet<Node> labelSet = cfgQ.nodesTaggedWithAll("isLabel").eval().nodes();
//			
//			for(Node labelNode : labelSet) {
//				AtlasSet<Node> predSet = dagQ.predecessors(Common.toQ(labelNode)).eval().nodes();
//				
//				//check flexible merge
//				if(predSet.size()>1 && Common.toQ(labelNode).nodes(XCSG.Loop).eval().nodes().size()==0) {
//					exitCtrl++;
//				}
//				
//				//check loop creation
//				if(Common.toQ(labelNode).nodes(XCSG.Loop).eval().nodes().size()>0) {
//					loopCreate ++;
//				}
//				
//				//check error exit
//				//// Loop Child ends with breaks and GOTOs, so just check if the predecessor of the label is in any of the loop child GOTOs
//				if(!loopChildNodeSet.contains(labelNode)&&Common.toQ(predSet).intersection(Common.toQ(loopChildNodeSet).nodes(XCSG.GotoStatement)).eval().nodes().size() > 0) {
//					errorExit ++;
//				}
//				
//				//check redundant
//				AtlasSet<Node> labelBodySet = dagQ.forward(Common.toQ(labelNode)).difference(Common.toQ(labelNode)).eval().nodes();
//				if(predSet.size()==1 && dagQ.predecessors(Common.toQ(labelBodySet)).eval().nodes().size()<2) {
//					redundant ++;
//				}
//				
//				//check unreachable
//				if(predSet.size() == 0) {
//					unreachable++;
//				}
//			}
//			br.write(num + "," + function.getAttr(XCSG.name).toString() + "," + labelSet.size() + "," + exitCtrl + "," + loopCreate + "," + errorExit + "," + redundant + "," + unreachable + "\n");
//			br.flush();	
//			
//		}
//		writer.close();
//	}
	
	private static void tagLabelCategoryNewHelper(int flag, Q cfgQ, Q dagQ, Node labelNode, AtlasSet<Node> predSetDag, AtlasSet <Node> loopChildNodeSet) {
		// input label flag: -2, -1 (miscellaneous), 0 (no entry), 1 (single entry), 2 (multiple entry)
		// Tags:
		final String MISC = "CATEGORY_Misc";
		final String UNREACH = "CATEGORY_Unreachable";
		final String LOOP = "CATEGORY_LoopCreation";
		final String FLEXMERGE = "CATEGORY_FlexMerge";
		final String LOOPEXIT = "CATEGORY_FlexLoopExit";
		final String REDUND = "CATEGORY_Redundant";
		
		// output: -1 (error), 0 (Unreachable), 1 (Loop Creation), 2 (Flexible Merge), 3 (Flexible loop exit), 4 (Redundant)
//		Set<Integer> result = new HashSet<Integer>();
		boolean hasTag = false;
		if(flag < 0) {
			labelNode.tag(MISC);
			return;
		}else if(flag == 0) {
			labelNode.tag(UNREACH);
			return;
		}
		
		if(flag == 2) { // multiple entry label
			if(labelNode.taggedWith(XCSG.Loop) && (cfgQ.predecessors(Common.toQ(labelNode)).nodes(XCSG.GotoStatement).intersection(Common.toQ(loopChildNodeSet))).eval().nodes().size() > 0) {
				// label tagged with XCSG.Loop AND at least one of its GOTOs is loop child
				labelNode.tag(LOOP); // loop creation
				hasTag = true;
			}else if(!labelNode.taggedWith(XCSG.Loop)) {
				// if it is not loop header
				if(loopChildNodeSet.contains(labelNode)) {
					// if it is a loop child
					labelNode.tag(FLEXMERGE); // flexible merge
					hasTag = true;
				}else if(Common.toQ(predSetDag).nodes(XCSG.GotoStatement).difference(Common.toQ(loopChildNodeSet)).eval().nodes().size() > 0) {
					// if not a loop child, AND has non-loopChild predecessors) 
					labelNode.tag(FLEXMERGE); // flexible merge
					hasTag = true;	
				}
			}
			
			// flexible loop exit
			if(!loopChildNodeSet.contains(labelNode) && Common.toQ(predSetDag).intersection(Common.toQ(loopChildNodeSet).nodes(XCSG.GotoStatement)).eval().nodes().size() > 0) {
				labelNode.tag(LOOPEXIT); // flexible loop exit
				hasTag = true; 
			}
			
		}else if(flag == 1) {  // single entry label
			
			// flexible loop exit
			if(!loopChildNodeSet.contains(labelNode) && Common.toQ(predSetDag).intersection(Common.toQ(loopChildNodeSet).nodes(XCSG.GotoStatement)).eval().nodes().size() > 0) {
				labelNode.tag(LOOPEXIT); // flexible loop exit
				hasTag = true; 
			}
			
			// redundant check
			AtlasSet<Node> labelBodySet = dagQ.forward(Common.toQ(labelNode)).eval().nodes();
			AtlasSet<Node> labelBodyEntryPredSet = dagQ.predecessors(Common.toQ(labelBodySet)).difference(Common.toQ(labelBodySet)).eval().nodes();
			if(labelBodyEntryPredSet.size()<2 && !labelNode.taggedWith(LOOPEXIT)) {
				// if no other entry to the label module, AND not loop exit, it is redundant. 
				labelNode.tag(REDUND); // redundant
				hasTag = true;
			}
			
			// flexible merge entry node check
			AtlasSet<Node> labelBodyEntrySet = dagQ.successors(Common.toQ(labelBodyEntryPredSet)).intersection(Common.toQ(labelBodySet)).eval().nodes();
			int lbeFlag = 0;
			if(labelBodyEntrySet.size() < 2) {
				lbeFlag = 1;
			}else {
				for(Node lbe : labelBodyEntrySet) {
					if(!lbe.taggedWith("isLabel")) {
						lbeFlag = 1;
						break;
					}
				}
			}
			if(lbeFlag == 0) {
				labelNode.tag(FLEXMERGE); // flexible merge
				hasTag = true;
			}
			
		}
		
		if(!hasTag) { // if still not tagged, tag as miscellaneous
			labelNode.tag(MISC);
		}
		return;
	}
	
	public static void tagLabelCategory() {
		
		// run DLI
		if(Common.universe().nodes("NATURAL_LOOP").eval().nodes().size()<1) {
			com.ensoftcorp.open.jimple.commons.loops.DecompiledLoopIdentification.recoverLoops();
			Log.info("DLI Done");
		}else {
			Log.info("No need for DLI");
		}
		
		// get all functions with labels
		AtlasSet<Node> labelFunctionSet = Common.universe().nodesTaggedWithAll("isLabel").parent().nodes(XCSG.Function).eval().nodes();
		
		
		AtlasSet<Node> unreachableSet = new AtlasHashSet<Node>();
		AtlasSet<Node> singleEntryLabelSet = new AtlasHashSet<Node>();
		AtlasSet<Node> multiEntryLabelSet = new AtlasHashSet<Node>();
		AtlasSet<Node> miscLabelSet = new AtlasHashSet<Node>();
		
		for(Node function: labelFunctionSet) {
			
			//CFG/DAG
			Q cfgQ = CommonQueries.cfg(Common.toQ(function));
			Q cfbeQ=cfgQ.edges(XCSG.ControlFlowBackEdge).retainEdges(); //Control flow back edge
			Q dagQ=cfgQ.differenceEdges(cfbeQ); // Control flow back edges removed
			
			//get map for loop children				
			AtlasSet <Node> loopNodeSet = cfgQ.nodes(XCSG.Loop).eval().nodes();
						
			AtlasSet <Node> loopChildNodeSet = Common.universe().edges(XCSG.LoopChild).
		        forward(Common.toQ(loopNodeSet)).retainNodes().eval().nodes();
			
			//go through all labels
			AtlasSet<Node> labelSet = cfgQ.nodesTaggedWithAll("isLabel").eval().nodes();
			
			int flag;
			for(Node labelNode : labelSet) {
				flag = -2;
				AtlasSet<Node> predSetDag = dagQ.predecessors(Common.toQ(labelNode)).eval().nodes();
				AtlasSet<Node> predSetCfg = cfgQ.predecessors(Common.toQ(labelNode)).eval().nodes();
				if(predSetCfg.size() == 0) {
					unreachableSet.add(labelNode);
					flag = 0;
				}else if(predSetCfg.size() == 1) {
					singleEntryLabelSet.add(labelNode);
					flag = 1;
				}else if(predSetCfg.size() > 1){
					multiEntryLabelSet.add(labelNode);
					flag = 2;
				}else {
					miscLabelSet.add(labelNode);
					flag = -1;
				}
				
				tagLabelCategoryNewHelper(flag, cfgQ, dagQ, labelNode, predSetDag, loopChildNodeSet);
			
			}
		}
		Log.info("NoEntry " + unreachableSet.size() + "; SingleEntry " + singleEntryLabelSet.size() + "; MultiEntry " + multiEntryLabelSet.size() + "; misc " + miscLabelSet.size());
		
	}
	
	
	public static void writeLabelCategoryByFunc(String filePath) throws IOException {
		
		final String MISC = "CATEGORY_Misc";
		final String UNREACH = "CATEGORY_Unreachable";
		final String LOOP = "CATEGORY_LoopCreation";
		final String FLEXMERGE = "CATEGORY_FlexMerge";
		final String LOOPEXIT = "CATEGORY_FlexLoopExit";
		final String REDUND = "CATEGORY_Redundant";
		
		// create directory
		new LabelAnalyzer().createDirectory();
		
		if(Common.universe().nodes(MISC, UNREACH, LOOP, FLEXMERGE, LOOPEXIT, REDUND).eval().nodes().size()<1) {
			Log.info("Start Tagging...");
			tagLabelCategory();
			Log.info("Tagging Done.");
		}else {
			Log.info("Already Categorized.");
		}
		
		FileWriter writer = new FileWriter(new File(filePath), true);
		writer.write("Function_number, Function_name, Total_labels, Flex_Merge, Loop_creation, Flex_Loop_Exit, Redundant, Unreachable, Misc\n");
		BufferedWriter br = new BufferedWriter(writer);
		
//		get all functions with labels
		AtlasSet<Node> labelFunctionSet = Common.universe().nodesTaggedWithAll("isLabel").parent().nodes(XCSG.Function).eval().nodes();
		
		// make a list so we can sort it
		List<Node> labelFunctionList = new ArrayList<Node>();
		
		for(Node function: labelFunctionSet) {
			labelFunctionList.add(function);
		}
		
		// custom sort
		Collections.sort(labelFunctionList,new Comparator<Node>() {
            @Override
            public int compare(Node n1, Node n2) {
            	// sort with name first, then number of nodes, then edges
                int value1 = n1.getAttr(XCSG.name).toString().compareTo(n2.getAttr(XCSG.name).toString());
                if (value1 == 0) {
                	Q cfgQ1 = CommonQueries.cfg(Common.toQ(n1));
                	Q cfgQ2 = CommonQueries.cfg(Common.toQ(n2));
                	int i1 = (int) cfgQ1.eval().nodes().size();
                	int i2 = (int) cfgQ2.eval().nodes().size();
                    int value2 = i2 - i1;
                    if (value2 == 0) {
                    	int i11 = (int) cfgQ1.eval().edges().size();
                    	int i22 = (int) cfgQ2.eval().edges().size();
                        return i22 - i11;
                    } else {
                        return value2;
                    }
                }
                return value1;
            }
        });
		
		int num = 0;
		for(Node function: labelFunctionList) { //the order is now sorted
			num++;
			//CFG/DAG
			Q cfgQ = CommonQueries.cfg(Common.toQ(function));
			
			//go through all labels
			AtlasSet<Node> labelSet = cfgQ.nodesTaggedWithAll("isLabel").eval().nodes();
			
			// count
			int flexMerge = 0;
			int loopCreate = 0;
			int flexLoopExit = 0;
			int redundant = 0;
			int unreachable = 0;
			int misc = 0;
			
			for(Node labelNode : labelSet) {
				if(labelNode.taggedWith(FLEXMERGE)) {
					flexMerge++;
				}
				if(labelNode.taggedWith(LOOP)) {
					loopCreate++;
				}
				if(labelNode.taggedWith(LOOPEXIT)) {
					flexLoopExit++;
				}
				if(labelNode.taggedWith(REDUND)) {
					redundant++;
				}
				if(labelNode.taggedWith(UNREACH)) {
					unreachable++;
				}
				if(labelNode.taggedWith(MISC)){
					misc++;
				}
			}
			
			// output
			br.write(num + "," + function.getAttr(XCSG.name).toString() + "," + labelSet.size() + "," + flexMerge + "," + loopCreate + "," + flexLoopExit + "," + redundant + "," + unreachable + "," + misc + "\n");
			br.flush();
		}
		writer.close();
		
	}
	
public static void writeLabelCategoryByLabel(String filePath) throws IOException {
		
		final String MISC = "CATEGORY_Misc";
		final String UNREACH = "CATEGORY_Unreachable";
		final String LOOP = "CATEGORY_LoopCreation";
		final String FLEXMERGE = "CATEGORY_FlexMerge";
		final String LOOPEXIT = "CATEGORY_FlexLoopExit";
		final String REDUND = "CATEGORY_Redundant";
		
		// create directory
		new LabelAnalyzer().createDirectory();
		
		if(Common.universe().nodes(MISC, UNREACH, LOOP, FLEXMERGE, LOOPEXIT, REDUND).eval().nodes().size()<1) {
			Log.info("Start Tagging...");
			tagLabelCategory();
			Log.info("Tagging Done.");
		}else {
			Log.info("Already Categorized.");
		}
		
		FileWriter writer = new FileWriter(new File(filePath), true);
		writer.write("Function_number, Function_name, Total_labels, Label_number, Label_name, Flex_Merge, Loop_creation, Flex_Loop_Exit, Redundant, Unreachable, Misc\n");
		BufferedWriter br = new BufferedWriter(writer);
		
		//	get all functions with labels
		AtlasSet<Node> labelFunctionSet = Common.universe().nodesTaggedWithAll("isLabel").parent().nodes(XCSG.Function).eval().nodes();
		
		// make a list so we can sort it
		List<Node> labelFunctionList = new ArrayList<Node>();
		
		for(Node function: labelFunctionSet) {
			labelFunctionList.add(function);
		}
		
		// custom sort
		Collections.sort(labelFunctionList,new Comparator<Node>() {
            @Override
            public int compare(Node n1, Node n2) {
            	// sort with name first, then number of nodes, then edges
                int value1 = n1.getAttr(XCSG.name).toString().compareTo(n2.getAttr(XCSG.name).toString());
                if (value1 == 0) {
                	Q cfgQ1 = CommonQueries.cfg(Common.toQ(n1));
                	Q cfgQ2 = CommonQueries.cfg(Common.toQ(n2));
                	int i1 = (int) cfgQ1.eval().nodes().size();
                	int i2 = (int) cfgQ2.eval().nodes().size();
                    int value2 = i2 - i1;
                    if (value2 == 0) {
                    	int i11 = (int) cfgQ1.eval().edges().size();
                    	int i22 = (int) cfgQ2.eval().edges().size();
                        return i22 - i11;
                    } else {
                        return value2;
                    }
                }
                return value1;
            }
        });
		
		int numFunc = 0;
		for(Node function: labelFunctionList) {
			numFunc++;
			//CFG/DAG
			Q cfgQ = CommonQueries.cfg(Common.toQ(function));
			
			//go through all labels
			AtlasSet<Node> labelSet = cfgQ.nodesTaggedWithAll("isLabel").eval().nodes();
			
			
			int numLabel = 0;
			for(Node labelNode : labelSet) {
				numLabel++;
				// count
				int flexMerge = 0;
				int loopCreate = 0;
				int flexLoopExit = 0;
				int redundant = 0;
				int unreachable = 0;
				int misc = 0;
				
				if(labelNode.taggedWith(FLEXMERGE)) {
					flexMerge++;
				}
				if(labelNode.taggedWith(LOOP)) {
					loopCreate++;
				}
				if(labelNode.taggedWith(LOOPEXIT)) {
					flexLoopExit++;
				}
				if(labelNode.taggedWith(REDUND)) {
					redundant++;
				}
				if(labelNode.taggedWith(UNREACH)) {
					unreachable++;
				}
				if(labelNode.taggedWith(MISC)){
					misc++;
				}
				
				String labelNumber = "" + numFunc + "_" + numLabel;
				// output
				br.write(numFunc + "," + function.getAttr(XCSG.name).toString() + "," + labelSet.size() + "," + labelNumber + "," + labelNode.getAttr(XCSG.name).toString() + "," + flexMerge + "," + loopCreate + "," + flexLoopExit + "," + redundant + "," + unreachable + "," + misc + "\n");
			}
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
		writer.write("Function_number, Function_name, nodes_CFG, edges_CFG, CtrlBlks_CFG, gotos, labels, nodes_PCG, edges_PCG, CtrlBlks_PCG\n");
		BufferedWriter br = new BufferedWriter(writer);
		
		//		get all functions with labels
		AtlasSet<Node> function_w_label = Common.universe().nodes("isLabel").parent().nodes(XCSG.Function).eval().nodes();
		
		// make a list so we can sort it
		List<Node> labelFunctionList = new ArrayList<Node>();
		
		for(Node function: function_w_label) {
			labelFunctionList.add(function);
		}
		
		// custom sort
		Collections.sort(labelFunctionList,new Comparator<Node>() {
            @Override
            public int compare(Node n1, Node n2) {
            	// sort with name first, then number of nodes, then edges
                int value1 = n1.getAttr(XCSG.name).toString().compareTo(n2.getAttr(XCSG.name).toString());
                if (value1 == 0) {
                	Q cfgQ1 = CommonQueries.cfg(Common.toQ(n1));
                	Q cfgQ2 = CommonQueries.cfg(Common.toQ(n2));
                	int i1 = (int) cfgQ1.eval().nodes().size();
                	int i2 = (int) cfgQ2.eval().nodes().size();
                    int value2 = i2 - i1;
                    if (value2 == 0) {
                    	int i11 = (int) cfgQ1.eval().edges().size();
                    	int i22 = (int) cfgQ2.eval().edges().size();
                        return i22 - i11;
                    } else {
                        return value2;
                    }
                }
                return value1;
            }
        });
		
		int num = 0;
		for(Node function: labelFunctionList) {
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
			AtlasSet<Node> pcg_seed = nodeOfInterestQ.eval().nodes();
			Q pcgQ = PCGFactory.create(cfgQ, Common.toQ(pcg_seed)).getPCG();
			
			AtlasSet<Node> gotoSet = cfgQ.nodes(XCSG.GotoStatement).eval().nodes();
			AtlasSet<Node> labelSet = cfgQ.nodes("isLabel").eval().nodes();
			AtlasSet<Node> cbEntrySet = cfgQ.nodesTaggedWithAny(XCSG.ControlFlowCondition, XCSG.Loop).eval().nodes();
			AtlasSet<Node> cbEntrySetPCG = pcgQ.nodesTaggedWithAny(XCSG.ControlFlowCondition, XCSG.Loop).eval().nodes();
			
			long nodes_CFG = cfgQ.eval().nodes().size();
			long edges_CFG = cfgQ.eval().edges().size();
			long CtrlBlks_CFG = cbEntrySet.size();
			long gotos = gotoSet.size();
			long labels = labelSet.size();
			long nodes_PCG = pcgQ.eval().nodes().size();
			long edges_PCG = pcgQ.eval().edges().size();
			long CtrlBlks_PCG = cbEntrySetPCG.size();
			
			br.write(num + "," + function.getAttr(XCSG.name).toString() + "," + nodes_CFG + "," + edges_CFG + "," + CtrlBlks_CFG + "," + gotos + "," + labels + "," + nodes_PCG + "," + edges_PCG + "," + CtrlBlks_PCG + "\n");
			br.flush();	
			
		}
		writer.close();
	}
	
	public static void writeSpaghetti() throws IOException {
		//write spaghetti code defined by 2015 paper, both CFG and PCG
		GOTO_GRAPH_DIRECTORY_NAME_PATTERN = "writeSpaghetti";
		
		// get saving directory
		new LabelAnalyzer().createDirectory();
		
		//		get all functions with labels
		AtlasSet<Node> function_w_label = Common.universe().nodesTaggedWithAll("isLabel").parent().nodes(XCSG.Function).eval().nodes();

		// make a list so we can sort it
		List<Node> labelFunctionList = new ArrayList<Node>();
		
		for(Node function: function_w_label) {
			labelFunctionList.add(function);
		}
		
		// custom sort
		Collections.sort(labelFunctionList,new Comparator<Node>() {
            @Override
            public int compare(Node n1, Node n2) {
            	// sort with name first, then number of nodes, then edges
                int value1 = n1.getAttr(XCSG.name).toString().compareTo(n2.getAttr(XCSG.name).toString());
                if (value1 == 0) {
                	Q cfgQ1 = CommonQueries.cfg(Common.toQ(n1));
                	Q cfgQ2 = CommonQueries.cfg(Common.toQ(n2));
                	int i1 = (int) cfgQ1.eval().nodes().size();
                	int i2 = (int) cfgQ2.eval().nodes().size();
                    int value2 = i2 - i1;
                    if (value2 == 0) {
                    	int i11 = (int) cfgQ1.eval().edges().size();
                    	int i22 = (int) cfgQ2.eval().edges().size();
                        return i22 - i11;
                    } else {
                        return value2;
                    }
                }
                return value1;
            }
        });
		
		int num = 0;
		for(Node function: labelFunctionList) {
			num++;
			Q cfgQ = CommonQueries.cfg(Common.toQ(function));
			Q cfbeQ=cfgQ.edges(XCSG.ControlFlowBackEdge).retainEdges(); //Control flow back edge
			Q dagQ=cfgQ.differenceEdges(cfbeQ); // Control flow back edges removed
			
			AtlasSet<Node> labelSet = cfgQ.nodes("isLabel").eval().nodes();
			
			boolean flag = false;
			
			for(Node labelNode : labelSet) {
				AtlasSet<Node> labelBodyNodeSet = dagQ.forward(Common.toQ(labelNode)).eval().nodes();
				AtlasSet<Node> labelPred = cfgQ.predecessors(Common.toQ(labelNode)).eval().nodes();
				if(Common.toQ(labelBodyNodeSet).difference(Common.toQ(labelPred)).nodes(XCSG.GotoStatement).eval().nodes().size() > 0) {
					// if found at least one label body with goto, print it
					flag = true;
					break;
				}
			}
			
			if(!flag) {
				continue;
			}
			
			AtlasSet<Node> gotoSet = cfgQ.nodesTaggedWithAll(XCSG.GotoStatement).eval().nodes();
			AtlasSet<Node> returnSet = cfgQ.nodesTaggedWithAll(XCSG.controlFlowExitPoint).eval().nodes();
			
			Markup markup = new Markup();
			markup.set(Common.toQ(labelSet), MarkupProperty.NODE_BACKGROUND_COLOR, Color.RED);
			markup.set(Common.toQ(gotoSet), MarkupProperty.NODE_BACKGROUND_COLOR, Color.YELLOW);
			markup.set(Common.toQ(returnSet), MarkupProperty.NODE_BACKGROUND_COLOR, Color.MAGENTA);
			
			
			// set file name
			String sourceFile = getQualifiedFunctionName(function);
			String methodName =  function.getAttr(XCSG.name).toString();
			
			// output CFG
			saveDisplayCFG(cfgQ.eval(), num, sourceFile, methodName, markup, false);
			
			
			// output PCG
			Q nodeOfInterestQ = Common.toQ(labelSet).union(Common.toQ(gotoSet)).union(Common.toQ(returnSet));
			AtlasSet<Node> pcg_seed = cfgQ.nodes(XCSG.ControlFlowCondition).union(nodeOfInterestQ).eval().nodes();
			
			Q pcg = PCGFactory.create(cfgQ, Common.toQ(pcg_seed)).getPCG();
			saveDisplayPCG(pcg.eval(), num, sourceFile, methodName, markup, false);
			
			
		}
		
	}

}
