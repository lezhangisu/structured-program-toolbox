package edu.iastate.structured.viewer;

import java.awt.Color;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import com.ensoftcorp.atlas.core.db.graph.Node;
import com.ensoftcorp.atlas.core.db.graph.Edge;
import com.ensoftcorp.atlas.core.db.graph.Graph;
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
import edu.iastate.structured.core.GraphAnalyzer;

import edu.iastate.structured.log.Log;

/**
 * For a selected function, displays the control flow graph. The edge back to
 * the start of the loop is highlighted in blue.
 */
public class StructuredParenthoodSmartView extends FilteringAtlasSmartViewScript {
	private Node prevFun = null;
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
		Q functions = filteredSelection.nodes(XCSG.Function);
		Q cf_nodes = filteredSelection.nodes(XCSG.ControlFlow_Node);
		
		if(!functions.eval().nodes().isEmpty()) {
			
			if(prevFun!= null && prevFun == functions.eval().nodes().one()) {
				Log.info("Re-Selected " + functions.eval().nodes().one().getAttr(XCSG.name));
				return null;
			}
			prevFun = functions.eval().nodes().one();
			
			Log.info("Function selected");
			Q cfg = CommonQueries.cfg(functions);
			
			GraphAnalyzer ga = new GraphAnalyzer();
			ga.analyze(cfg);
			
			Map<Node, Node> map_parent = ga.getParentMap();
			
			AtlasSet<Node> allSelectable = cfg.nodesTaggedWithAny("STRUCT_SELECTABLE").eval().nodes();
			
			AtlasSet<Edge> edgeSet = new AtlasHashSet<Edge>();
			
			AtlasSet<Node> nodeSet = new AtlasHashSet<Node>();
			
			for(Node n : allSelectable) {
				if(map_parent.keySet().contains(n)) {
					Edge e = Graph.U.createEdge(map_parent.get(n), n);
					edgeSet.add(e);
				}else {
					nodeSet.add(n);
				}
			}
			
			Q parenthood = Common.toQ(edgeSet).union(Common.toQ(nodeSet));
			
								
			Markup m = new Markup();
//			m.setEdge(Common.codemap().edges(XCSG.ControlFlowBackEdge), MarkupProperty.EDGE_COLOR, Color.BLUE);

			Log.info("Function finished");
			return new StyledResult(parenthood, m);
			
		}
		
		return null;	
		
	}

	@Override
	public String getTitle() {
		return "Structured Code View - Parenthood";
	}
}