package edu.iastate.labels.viewer;

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

import edu.iastate.labels.core.LabelAnalyzer;
import edu.iastate.labels.viewer.log.Log;

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
		Q label_node = filteredSelection.nodes("isLabel");
		Q f = Common.empty();
		Q cfg = Common.empty();

		if(!function.eval().nodes().isEmpty()) {
			// if no function, return original graph
			Log.info("Function " + function.eval().nodes().one().getAttr(XCSG.name) + " Selected");
			cfg = CommonQueries.cfg(function);

			// pre-process the graph
//			if(previous_function!=null && function.eval().nodes().one().equals(previous_function)) {
//				Log.info("Preprocess Already Done");
//			}else {
//				preprocess(function);
//			}
//			previous_function = function.eval().nodes().one();

			Markup m = new Markup();
			m.setEdge(Common.codemap().edges(XCSG.ControlFlowBackEdge), MarkupProperty.EDGE_COLOR, Color.BLUE);

			return new StyledResult(cfg, m);

		}else if(!label_node.eval().nodes().isEmpty()) {
//			Log.info("Control Flow Condition Node \" " + cf_condition.eval().nodes().one().getAttr(XCSG.name) + "\" Selected");

			// if selected a control flow node, parse for subgraph
			function = label_node.parent().nodes(XCSG.Function); // find the parent function
			cfg = CommonQueries.cfg(function); // get cfg from the function
	

			// list [entry, subgraph, exits]
			List<AtlasSet<Node>> subgraph = LabelAnalyzer.getModule(cfg, label_node.eval().nodes().getFirst());

			// log subgraph info
			Log.info("Subgraph size: " + (subgraph.get(1).size()+subgraph.get(0).size()+subgraph.get(2).size()));
			Log.info("Body size: " + subgraph.get(1).size());
			Log.info("Entry size: " + subgraph.get(0).size());
			Log.info("Exit size: " + subgraph.get(2).size());

			// init the markup
			Markup m = new Markup();
			if(subgraph.size() >= 3) {
				// mark nodes and edges within this subgraph with yellow color
				m.setNode(Common.toQ(subgraph.get(1)), MarkupProperty.NODE_BACKGROUND_COLOR, Color.YELLOW.darker());
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
//			Log.info("Ordinary Control Flow Node Selected");

			f = cf_node.parent().nodes(XCSG.Function); // find the parent function
			cfg = CommonQueries.cfg(f); // get cfg from the function

			Markup m = new Markup();
			m.setEdge(Common.codemap().edges(XCSG.ControlFlowBackEdge), MarkupProperty.EDGE_COLOR, Color.BLUE);

			return new StyledResult(cfg, m);
		}
		return null;

	}


	@Override
	public String getTitle() {
		return "scode Label View";
	}
}
