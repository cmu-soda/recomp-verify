package recomp;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import cmu.isr.ts.LTS;
import cmu.isr.ts.lts.SafetyUtils;
import net.automatalib.words.Word;
import tlc2.TLC;

public class FormulaSeparation {
	public static String isCandSepInvariant(final String tla, final String cfg, final String tlaComp, final String cfgComp) {
    	TLC tlc = new TLC();
    	tlc.modelCheck(tla, cfg);
    	final LTS<Integer, String> lts = tlc.getLTSBuilder().toIncompleteDetAutIncludingAnErrorState();
    	
    	if (SafetyUtils.INSTANCE.ltsIsSafe(lts)) {
    		System.out.println("TRUE");
    	}
    	else {
    		TLC tlcComp = new TLC();
    		tlcComp.initialize(tlaComp, cfgComp);
    		final Set<String> alphabet = tlcComp.actionsInSpec();
    		
    		// if candSep isn't an invariant, return a trace that should be covered by the formula
    		final List<String> trace = SafetyUtils.INSTANCE.findErrorTrace(lts)
    				.stream()
    				.filter(act -> {
    					final String abstractAct = act.replaceAll("\\..*$", "");
    					return alphabet.contains(abstractAct);
    				})
    				.collect(Collectors.toList());
    		
    		String strLastIdx = "";
    		List<String> strTimeActs = new ArrayList<>();
    		for (int i = 0; i < trace.size(); ++i) {
    			final String time = "T" + i;
    			final String act = trace.get(i).replace(".", "");
    			final String timeAct = time + "->" + act;
    			strTimeActs.add(timeAct);
    			strLastIdx = time;
    		}
    		final String strTrace = String.join(" + ", strTimeActs);
    		final String str = "lastIdx = " + strLastIdx + "\n" +
    				"(" + strTrace + ") in path";
    		System.out.println(str);
    	}
    	
    	return null;
	}
}
