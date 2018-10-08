package edu.iastate.scode.gotos;

import com.ensoftcorp.atlas.core.db.graph.Node;
import com.ensoftcorp.atlas.core.query.Q;
import com.ensoftcorp.atlas.core.script.Common;
import com.ensoftcorp.atlas.core.xcsg.XCSG;

public class GotoParser {
	
	private static final String GOTO = "goto";
	
//	private static final String gotos = "/home/payas/gotos.txt";

	/*public static void parse(String filepath) throws IOException {
		
		List<Integer> lineNumbers = new ArrayList<Integer>();
		
		String st = "";
		
		File file = new File(filepath);
		
		BufferedReader br = new BufferedReader(new FileReader(file));
		
		int lineCounter = 0;
		
		while((st = br.readLine()) != null) {
			lineCounter++;
			if(st.contains(GOTO)) {
				lineNumbers.add(lineCounter);
			}
		}
		
		br.close();
		
		File results = new File(gotos);
		
		BufferedWriter bw = new BufferedWriter(new FileWriter(results));
		
		for(Integer item: lineNumbers) {
			bw.write(item + "\n");
		}
		
		bw.close();
		
		
	}*/
	
	public static void tagGotos() {
		Q controlFlow = Common.universe().nodes(XCSG.ControlFlow_Node);
		
		for(Node controlFlowNode : controlFlow.eval().nodes()) {
			String name = controlFlowNode.getAttr(XCSG.name).toString();
			if(name.contains(GOTO)) {
				controlFlowNode.tag(GOTO);
			}
		}
	}

}
