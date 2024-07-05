package recomp;

import java.util.HashMap;
import java.util.Map;
import java.util.Random;

import cmu.isr.assumption.WAHelper;
import cmu.isr.ts.LTS;
import cmu.isr.ts.lts.CompactDetLTS;
import cmu.isr.ts.nfa.Determinization;
import net.automatalib.automata.fsa.DFA;
import net.automatalib.automata.fsa.impl.compact.CompactDFA;
import tlc2.TLC;

public class WeakestAssumption {

	public static LTS<Integer, String> calc(final String tla, final String cfg) {
    	TLC tlc = new TLC();
    	tlc.modelCheck(tla, cfg);
    	LTS<Integer, String> lts = tlc.getLTSBuilder().toIncompleteDetAutIncludingAnErrorState();
    	DFA<Integer, String> dfa = Determinization.INSTANCE.determinize(lts);
    	return WAHelper.INSTANCE.makeWA( new CompactDetLTS((CompactDFA) dfa) );
	}
	
	public static String calcSymbolic(final String tla, final String cfg) {
    	TLC tlc = new TLC();
    	tlc.modelCheck(tla, cfg);
    	LTS<Integer, String> lts = tlc.getLTSBuilder().toIncompleteDetAutIncludingAnErrorState();
    	lts = AutomataLibUtils.minimizeLTS(lts);
    	StringBuilder alsLTS = new StringBuilder();
    	
    	// create sigs for the alphabet
    	for (final String act : lts.getInputAlphabet()) {
    		final String alsAct = act.replace(".", dotReplacement);
    		alsLTS.append("one sig " + alsAct + " extends Act {} {}\n");
    	}
    	alsLTS.append("\n");
    	
    	// keep track of the sig name for each state
    	Map<Integer, String> stateSigNames = new HashMap<>();
    	
    	// create sigs for the states
    	for (final Integer state : lts.getStates()) {
    		final boolean initState = lts.getInitialStates().contains(state);
    		final boolean piState = lts.isErrorState(state);
    		final String stateName = piState ? "PI" : "S" + state;
    		if (piState || coinFlip(0.3)) {
        		final String alsState = "one sig " + stateName + " extends State {} {\n"
        				+ "	init = " + (initState ? "True" : "False") + "\n"
        				+ "	error = " + (piState ? "True" : "False") + "\n"
        				+ "}\n";
        		alsLTS.append(alsState);
        		stateSigNames.put(state, stateName);
    		}
    	}
    	alsLTS.append("\n");
    	
    	// create sigs for the transitions
    	int transitionNum = 1;
    	for (final Integer src : lts.getStates()) {
    		for (final String act : lts.getInputAlphabet()) {
				for (final Integer dst : lts.getTransitions(src, act)) {
					if (stateSigNames.containsKey(src) && stateSigNames.containsKey(dst)) {
						final String srcSigName = stateSigNames.get(src);
						final String dstSigName = stateSigNames.get(dst);
			    		final String alsAct = act.replace(".", dotReplacement);
						final String alsTransition = "one sig T" + transitionNum++ + " extends Transition {} {\n"
								+ "	src = " + srcSigName + "\n"
								+ "	act = " + alsAct + "\n"
								+ "	dst = " + dstSigName + "\n"
								+ "}\n";
			    		alsLTS.append(alsTransition);
					}
				}
    		}
    	}
    	
    	return alsTemplate + alsLTS.toString();
	}
	
	private static Random rand = new Random();
	
	private static boolean coinFlip(double ub) {
		//return rand.nextDouble() < ub;
		return true;
	}
	
	private static final String dotReplacement = "X";
	
	private static final String alsTemplate = "open util/boolean\n"
			+ "\n"
			+ "/* LTS signatures */\n"
			+ "abstract sig Act {}\n"
			+ "\n"
			+ "abstract sig State {\n"
			+ "	init : Bool,\n"
			+ "	error : Bool\n"
			+ "}\n"
			+ "\n"
			+ "abstract sig Transition {\n"
			+ "	src : State,\n"
			+ "	act : Act,\n"
			+ "	dst : State\n"
			+ "}\n"
			+ "\n"
			+ "// returns all \"predecessor\" transitions\n"
			+ "fun predTransitions[t : Transition] : set Transition {\n"
			+ "	{ p : Transition | p.dst = t.src }\n"
			+ "}\n"
			+ "\n"
			+ "\n"
			+ "/* Formula signatures (represented by a DAG) */\n"
			+ "abstract sig Formula {\n"
			+ "	children : set Formula\n"
			+ "}\n"
			+ "fact {\n"
			+ "	// eliminates cycles in formula nodes\n"
			+ "	all f : Formula | f not in f.^children\n"
			+ "}\n"
			+ "\n"
			+ "one sig Root extends Formula {} {\n"
			+ "	one children\n"
			+ "}\n"
			+ "fact {\n"
			+ "	// all formulas must be a sub-formula of the root\n"
			+ "	all f : Formula | f in Root.*children\n"
			+ "}\n"
			+ "\n"
			+ "sig Not extends Formula {\n"
			+ "	child : Formula\n"
			+ "} {\n"
			+ "	children = child\n"
			+ "}\n"
			+ "\n"
			+ "sig And, Implies, Or extends Formula {\n"
			+ "	left : Formula,\n"
			+ "	right : Formula\n"
			+ "} {\n"
			+ "	children = left + right\n"
			+ "}\n"
			+ "\n"
			+ "sig OnceAct extends Formula {\n"
			+ "	act : Act\n"
			+ "} {\n"
			+ "	no children\n"
			+ "}\n"
			+ "\n"
			+ "sig TT, FF extends Formula {} {\n"
			+ "	no children\n"
			+ "}\n"
			+ "\n"
			+ "\n"
			+ "/* formula semantics, i.e. when t |= f, where t is a transition and f is a formula */\n"
			+ "one sig Semantics {\n"
			+ "	satisfies : set (Transition -> Formula)\n"
			+ "} {\n"
			+ "	all t : Transition, f : Root | t->f in satisfies iff t->f.children in satisfies\n"
			+ "	all t : Transition, f : TT | t->f in satisfies\n"
			+ "	all t : Transition, f : FF | t->f not in satisfies\n"
			+ "	all t : Transition, f : Not | t->f in satisfies iff (t->f.child not in satisfies)\n"
			+ "	all t : Transition, f : And | t->f in satisfies iff (t->f.left in satisfies and t->f.right in satisfies)\n"
			+ "	all t : Transition, f : Implies | t->f in satisfies iff (t->f.left in satisfies implies t->f.right in satisfies)\n"
			+ "	all t : Transition, f : Or | t->f in satisfies iff (t->f.left in satisfies or t->f.right in satisfies)\n"
			+ "	all t : Transition, f : OnceAct | t->f in satisfies iff\n"
			+ "		((f.act = t.act) or (some predTransitions[t] and predTransitions[t]->f in satisfies))\n"
			+ "}\n"
			+ "\n"
			+ "\n"
			+ "/* main */\n"
			+ "run {\n"
			+ "	// find a formula that separates \"good\" transitions from \"bad\" ones. we assume that the PI state is a sink,\n"
			+ "	// i.e. the PI state has no outgoing transitions.\n"
			+ "	all t : Transition | (t.dst.error = False) iff (t->Root in Semantics.satisfies)\n"
			+ "	minsome children\n"
			+ "} for 10 Formula\n"
			+ "\n";
}
