package edu.iastate.structured.core;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Map;
import java.io.BufferedWriter;
import java.io.PrintWriter;

import com.ensoftcorp.atlas.core.db.graph.Edge;
import com.ensoftcorp.atlas.core.db.graph.Graph;
import com.ensoftcorp.atlas.core.db.graph.Node;
import com.ensoftcorp.atlas.core.db.set.AtlasSet;
import com.ensoftcorp.atlas.core.script.Common;
import com.ensoftcorp.open.c.commons.analysis.CommonQueries;
import com.ensoftcorp.atlas.core.xcsg.XCSG;
import com.ensoftcorp.atlas.core.query.Q;

import edu.iastate.structured.log.Log;

public class Stats {
	public static void writeStats(String filePath) throws IOException {	
		FileWriter writer = new FileWriter(new File(filePath));
		writer.write("Function,Nodes_CFG,Edges_CFG,Nodes_CG,Nodes_RCG,Num_of_CB\n");
		
		//		get all functions with labels
		Q app = Common.universe().nodes(XCSG.Project);
		AtlasSet<Node> functionSet = app.contained().nodes(XCSG.Function).eval().nodes();
		
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
	
	public static void writeParentStats(String filePath) throws IOException {	
		FileWriter writer = new FileWriter(new File(filePath), true);
		writer.write("Function, #_of_CB, #_of_GOTO, #_of_outerBlock\n");
		
		
		//		get all functions with labels
		Q app = Common.universe().nodes(XCSG.Project);
		AtlasSet<Node> functionSet = app.contained().nodes(XCSG.Function).eval().nodes();
		
		
		long cnt = 0;
		boolean flag = false;
		for(Node function: functionSet) {
			cnt ++;
			Log.info(cnt +  " | " + function.getAttr(XCSG.name).toString());
			
			if(cnt < 0) {
				continue;
			}
			
//			if(
//					function.getAttr(XCSG.name).toString().contains("ip2name")
//					||function.getAttr(XCSG.name).toString().contains("x_route")
//					||function.getAttr(XCSG.name).toString().contains("setpath")
//					||function.getAttr(XCSG.name).toString().contains("pcreate")
//					||function.getAttr(XCSG.name).toString().contains("adump")
//					||function.getAttr(XCSG.name).toString().contains("x_echo")
//					||function.getAttr(XCSG.name).toString().contains("x_creat")
//					||function.getAttr(XCSG.name).toString().contains("bpdump")
//					||function.getAttr(XCSG.name).toString().contains("ibput")
//					||function.getAttr(XCSG.name).toString().contains("dgalloc")
//					||function.getAttr(XCSG.name).toString().contains("rfdump")
//					||function.getAttr(XCSG.name).toString().contains("sysinit")
//					||function.getAttr(XCSG.name).toString().contains("x_cat")
//					||function.getAttr(XCSG.name).toString().contains("rwhod")
//					||function.getAttr(XCSG.name).toString().contains("rwhoind")
//					||function.getAttr(XCSG.name).toString().contains("sndrarp")
//					||function.getAttr(XCSG.name).toString().contains("tqdump")
//					||function.getAttr(XCSG.name).toString().contains("dgdump")
//					||function.getAttr(XCSG.name).toString().contains("dskqopt")
//					||function.getAttr(XCSG.name).toString().contains("ttyread")
//					||function.getAttr(XCSG.name).toString().contains("ethstrt")
//					) {
////				flag = true;
//				writer.write(function.getAttr(XCSG.name).toString() + "," + "\n");
//				continue;
//			}
			
//			if (!flag) {
//				continue;
//			}
			
			Q cfgQ = CommonQueries.cfg(Common.toQ(function));
			
			Structured.analyze(cfgQ.eval());
			
			Map<Node, Node> map_parent = Structured.getParentMap(cfgQ.eval());
			
			AtlasSet<Node> allSelectable = cfgQ.nodes(XCSG.ControlFlowCondition, "LoopByLabel").eval().nodes();
			
			
			long cntOuterBlock = 0;
			
			for(Node n : allSelectable) {
				if(!map_parent.keySet().contains(n)) {
					cntOuterBlock ++;
				}
			}
			
			long cntGoto = cfgQ.nodes(XCSG.GotoStatement).eval().nodes().size();
			
			BufferedWriter br = new BufferedWriter(writer);			
			
			br.write(function.getAttr(XCSG.name).toString() + "," + allSelectable.size() + "," + cntGoto + "," + cntOuterBlock + "\n");

			br.flush();
			
		}
		writer.close();
	}


}
