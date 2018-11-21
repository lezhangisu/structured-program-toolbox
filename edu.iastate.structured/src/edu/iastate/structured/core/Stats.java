package edu.iastate.structured.core;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;

import com.ensoftcorp.atlas.core.db.graph.Node;
import com.ensoftcorp.atlas.core.db.set.AtlasSet;
import com.ensoftcorp.atlas.core.script.Common;
import com.ensoftcorp.open.c.commons.analysis.CommonQueries;
import com.ensoftcorp.atlas.core.xcsg.XCSG;
import com.ensoftcorp.atlas.core.query.Q;

public class Stats {
	public static void writeStats(String filePath) throws IOException {	
		FileWriter writer = new FileWriter(new File(filePath));
		writer.write("Function,Nodes_CFG,Edges_CFG,Nodes_CG,Nodes_RCG,Num_of_CB\n");
		
		//		get all functions with labels
		AtlasSet<Node> functionSet = Common.universe().nodes(XCSG.Function).eval().nodes();
		
		for(Node function: functionSet) {
			Q cfg = CommonQueries.cfg(Common.toQ(function));
			long nodesCfg = cfg.eval().nodes().size();
			long edgesCfg = cfg.eval().edges().size();
			
			Q cg = CommonQueries.cg(Common.toQ(function));
			Q rcg = CommonQueries.rcg(Common.toQ(function));
			
			long nodesCg = cg.eval().nodes().size();
			long nodesRcg = rcg.eval().nodes().size();
			
			
			AtlasSet<Node> selectable = cfg.nodesTaggedWithAny("isLabel", XCSG.Loop, XCSG.ControlFlowCondition).eval().nodes();
			long numCB = selectable.size();
			
			writer.write(function.getAttr(XCSG.name).toString() + "," + nodesCfg + "," + edgesCfg + "," + nodesCg + "," + nodesRcg + "," + numCB + "\n");
			
		}
		writer.close();
	}

}
