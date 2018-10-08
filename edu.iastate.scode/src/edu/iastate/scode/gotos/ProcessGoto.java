package edu.iastate.scode.gotos;

import java.util.HashMap;
import java.util.Map;

import com.ensoftcorp.atlas.core.db.graph.Edge;
import com.ensoftcorp.atlas.core.db.graph.Graph;
import com.ensoftcorp.atlas.core.db.graph.GraphElement;
import com.ensoftcorp.atlas.core.db.graph.Node;
import com.ensoftcorp.atlas.core.db.set.AtlasHashSet;
import com.ensoftcorp.atlas.core.db.set.AtlasSet;
import com.ensoftcorp.atlas.core.query.Q;
import com.ensoftcorp.atlas.core.script.Common;
import com.ensoftcorp.atlas.core.script.CommonQueries;
import com.ensoftcorp.atlas.core.xcsg.XCSG;
import com.ensoftcorp.open.pcg.common.PCGFactory;

public class ProcessGoto {
	
	private static Map<Node,AtlasSet<Node>> parentMap = new HashMap<Node,AtlasSet<Node>>();
	
	public static void process() {
		
		GotoParser.tagGotos();
		
		Q functions = Common.universe().nodes(XCSG.Function);
		
		for(Node function: functions.eval().nodes()) {
			processFunctionUsingPCG(function);
		}
	}
	
	public static Q processFunctionUsingPCG(Node function) {
		Q cfg = CommonQueries.cfg(Common.toQ(function));
		Q gotos = cfg.nodes("goto");
		Q labels = cfg.successors(gotos);
		AtlasSet<Node> gotoAndLabels = gotos.union(labels).eval().nodes();
		AtlasSet<Node> events = new AtlasHashSet<Node>();
		events.addAll(cfg.eval().nodes());
		for(Node gotoOrLabel : gotoAndLabels) {
			events.remove(gotoOrLabel);
		}
		Q transformedCFG = PCGFactory.create(cfg, Common.toQ(events)).getPCG();
		
		return transformedCFG;
	}
	
	public static Q processFunction(Node function) {
		Q cfg = CommonQueries.cfg(Common.toQ(function));
		AtlasSet<Node> transformedCFGNodes = new AtlasHashSet<Node>();
		transformedCFGNodes.addAll(cfg.eval().nodes());
		AtlasSet<Edge> transformedCFGEdges = new AtlasHashSet<Edge>();
		transformedCFGEdges.addAll(cfg.eval().edges());
		AtlasSet<GraphElement> transformedCFGElements = new AtlasHashSet<GraphElement>();
		Q gotos = cfg.nodes("goto");
		for(Node gotoNode : gotos.eval().nodes()) {
			Q gotoPredecessor = cfg.reverseStep(Common.toQ(gotoNode));
			Node gotoPredecessorNode = gotoPredecessor.roots().eval().nodes().one();
			Edge gotoPredecessorEdge = gotoPredecessor.eval().edges().one();
			Q label = cfg.forwardStep(cfg.forwardStep(Common.toQ(gotoNode)));
			Node labelNode = cfg.forwardStep(Common.toQ(gotoNode)).eval().nodes().one();
			AtlasSet<Edge> labelEdges = label.eval().edges();
			Node labelSuccessor = label.leaves().eval().nodes().one();
			transformedCFGNodes.remove(gotoNode);
			transformedCFGNodes.remove(labelNode);
			for(Edge labelEdge : labelEdges) {
				transformedCFGEdges.remove(labelEdge);
			}
			transformedCFGEdges.remove(gotoPredecessorEdge);
			Edge e = Graph.U.createEdge(gotoPredecessorNode, labelSuccessor);
			transformedCFGEdges.add(e);
		}
		
		transformedCFGElements.addAll(transformedCFGNodes);
		transformedCFGElements.addAll(transformedCFGEdges);
		
		Q transformedCFG = Common.toQ(Common.toGraph(transformedCFGElements));
		
		
		
		return transformedCFG;
	}
	
	public static void preprocess() {
		Q ifConditions = Common.universe().nodes(XCSG.ControlFlowCondition);
		
		for(Node ifCondition : ifConditions.eval().nodes()) {
			Q cfg = CommonQueries.cfg(Common.toQ(ifCondition).containers().nodes(XCSG.Function));
			Q cfgLeaves = cfg.leaves();
			AtlasSet<Node> branchNodes = cfg.successors(Common.toQ(ifCondition)).eval().nodes();
			Q intersectionGraph = cfg;
			for(Node branchNode : branchNodes) {
				Q subGraph = cfg.between(Common.toQ(branchNode), cfgLeaves);
				intersectionGraph = subGraph.intersection(intersectionGraph);
			}
			Q mergePoint = intersectionGraph.roots();
			Q ifConditionBody = cfg.between(Common.toQ(ifCondition), mergePoint);
			Q gotos = ifConditionBody.nodes("goto");
			for(Node gotoNode : gotos.eval().nodes()) {
				if(parentMap.containsKey(gotoNode)) {
					AtlasSet<Node> childSet = parentMap.get(gotoNode);
					childSet.add(ifCondition);
					parentMap.put(gotoNode, childSet);
				}
				else {
					AtlasSet<Node> childSet = new AtlasHashSet<Node>();
					childSet.add(ifCondition);
					parentMap.put(gotoNode, childSet);
				}
			}
			
		}
	}

}
