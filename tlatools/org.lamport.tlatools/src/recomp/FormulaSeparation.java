package recomp;

import java.io.BufferedReader;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import cmu.isr.ts.LTS;
import cmu.isr.ts.lts.SafetyUtils;
import lts.SymbolTable;
import net.automatalib.words.Word;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpDefNode;
import tlc2.TLC;
import tlc2.Utils;
import tlc2.tool.impl.FastTool;

public class FormulaSeparation {
	
	public static String synthesizeSepInvariant(final String tlaSys, final String cfgSys, final String tlaComp, final String cfgComp) {
    	SymbolTable.init();
    	
    	// config for producing positive traces
    	final String cfgPosTraces = "pos_traces.cfg";
    	Utils.writeFile(cfgPosTraces, "SPECIFICATION Spec\nINVARIANT CandSep");
    	
    	//final List<String> rawComponents = Decomposition.decompAll(tla, cfg);
    	//final List<String> components = Composition.symbolicCompose(tla, cfg, "CUSTOM", "recomp_map.csv", rawComponents);
    	
    	final String initPosTrace = "one sig PT1 extends PosTrace {} {\n"
    			+ "	 lastIdx = T3\n"
    			+ "	 (T0->SndPreparerm1 + T1->SndPreparerm2 + T2->RcvCommitrm2 + T3->RcvCommitrm1) in path\n"
    			+ "}";
    	List<String> posTraces = new ArrayList<>();
    	posTraces.add(initPosTrace);
    	
    	List<String> invariants = new ArrayList<>();
    	boolean formulaSeparates = false;
    	
    	while (!formulaSeparates) {
    		final String invariant = invariants.isEmpty() ? "TRUE" : "(" + String.join(") /\\ (", invariants) + ")";
        	final String tlaCompHV = writeHistVarsSpec(tlaComp, cfgComp, invariant, true);
        	final String negTrace = isCandSepInvariant(tlaCompHV, cfgComp, tlaComp, cfgComp, "NT", "NegTrace");
    		formulaSeparates = negTrace.equals("TRUE");
    		boolean isInvariant = false;
    		
    		if (!formulaSeparates && !isInvariant) {
    			// turn the formula into an invariant
    			final String formula = synthesizeFormula(negTrace, posTraces);
    			
    			final int ptNum = posTraces.size() + 1;
    			final String ptName = "PT" + ptNum;
    	    	final String tlaSysHV = writeHistVarsSpec(tlaSys, cfgSys, formula, false);
    			final String posTrace = isCandSepInvariant(tlaSysHV, cfgPosTraces, tlaComp, cfgComp, ptName, "PosTrace");
    			isInvariant = posTrace.equals("TRUE");
    			if (isInvariant) {
    				invariants.add(formula);
    				System.out.println("found new invariant: " + formula);
    			}
    			else {
    				posTraces.add(posTrace);
    				System.out.println("attempting to strengthen to be an invariant: " + formula);
        			System.out.println("posTrace:\n" + posTrace);
    			}
				System.out.println();
    		}
    	}
    	
    	return invariants.isEmpty() ? "TRUE" : "(" + String.join(") /\\ (", invariants) + ")";
	}
	
	private static String synthesizeFormula(final String negTrace, final List<String> posTraces) {
		final String alloyFormulaInferFile = "formula_infer.als";

		writeAlloyFormulaInferFile(alloyFormulaInferFile, negTrace, posTraces);
		
		// life would be so much easier if this just worked
		//final String formula = AlsSynthesis.INSTANCE.synthFormulaFromAls(alloyFormulaInferFile, true);
		
		StringBuilder formulaBuilder = new StringBuilder();
		try {
			final String[] cmd = {"java", "-Xmx25G", "-jar", alloyFormlaInferJar, "-f", alloyFormulaInferFile, "--tla"};
			BufferedReader reader = Runtime.getRuntime().exec(cmd).inputReader();
			String line = null;
			while ((line = reader.readLine()) != null) {
				formulaBuilder.append(line);
			}
		}
		catch (Exception e) {
			e.printStackTrace();
			return "";
		}
		
		// is the formula an invariant?
		return formulaBuilder.toString();
	}
	
	private static void writeAlloyFormulaInferFile(final String fileName, final String negTrace, final List<String> posTraces) {
		final String alloyFormulaInfer = baseAlloyFormulaInfer
				+ "\n" + negTrace + "\n\n"
				+ String.join("\n", posTraces) + "\n";
		Utils.writeFile(fileName, alloyFormulaInfer);
	}
	
	private static String writeHistVarsSpec(final String tla, final String cfg, final String candSep, boolean candSepInActions) {
    	final String tlaCompBaseName = tla.replaceAll("\\.tla", "");
    	final String specName = tlaCompBaseName + "_hist";
    	
		TLC tlc = new TLC();
		tlc.initialize(tla, cfg);
		
		final Set<String> onceVars = tlc.actionsInSpec()
				.stream()
				.map(v -> "once" + v)
				.collect(Collectors.toSet());

    	final FastTool ft = (FastTool) tlc.tool;
		final String moduleName = tlc.getModelName();
		final ModuleNode mn = ft.getModule(moduleName);
		List<OpDefNode> moduleNodes = Utils.toArrayList(mn.getOpDefs())
				.stream()
				// only retain module for the .tla file
				.filter(d -> moduleName.equals(d.getOriginallyDefinedInModuleNode().getName().toString()))
				.filter(d -> !d.getName().toString().equals("vars")) // remove the vars decl; we insert this manually
				.collect(Collectors.toList());
		
		final String specBody = moduleNodes
				.stream()
				.map(d -> {
					final String dname = d.getName().toString();
					if (tlc.actionsInSpec().contains(dname)) {
						d.addOnceVars(onceVars,candSepInActions);
					}
					else if (dname.equals("Init")) {
						d.addOnceInitVars(onceVars);
					}
					return d;
				 })
				.map(d -> {
					// TODO fix this ugly hack
					if (d.getName().toString().equals("RMs")) {
						return d.toTLA() + "\n\nCandSep == " + candSep;
					}
					return d.toTLA();
				 })
				.collect(Collectors.joining("\n\n"));
		
        final String specDecl = "--------------------------- MODULE " + specName + " ---------------------------";
        final String endModule = "=============================================================================";
        
        final List<String> moduleWhiteList =
        		Arrays.asList("Bags", "FiniteSets", "Functions", "Integers", "Json", "Naturals",
        				"NaturalsInduction", "RealTime", "Sequences", "SequencesExt", "TLC", "TLCExt");
        ArrayList<String> moduleNameList = Utils.filterArrayWhiteList(moduleWhiteList, ft.getModuleNames());

        final String moduleList = String.join(", ", moduleNameList);
        final String varList = String.join(", ", Utils.union(tlc.stateVarsInSpec(), onceVars));
        final String modulesDecl = moduleList.isEmpty() ? "" : "EXTENDS " + moduleList;
        final String varsDecl = "VARIABLES " + varList;
        final String varsListDecl = "vars == <<" + varList + ">>";
        
        StringBuilder builder = new StringBuilder();
        builder.append(specDecl).append("\n");
        builder.append(modulesDecl).append("\n");
        builder.append("\n");
        builder.append(varsDecl).append("\n");
        builder.append("\n");
        builder.append(varsListDecl).append("\n");
        builder.append("\n");
        builder.append(specBody);
        builder.append("\n");
        builder.append(endModule).append("\n");

        final String fileName = specName + ".tla";
        final String file = fileName;
        Utils.writeFile(file, builder.toString());
        
        return specName;
	}
	
	public static String isCandSepInvariant(final String tla, final String cfg,
			final String tlaAlphabetSpec, final String cfgAlphabetSpec, final String name, final String ext) {
    	TLC tlc = new TLC();
    	tlc.modelCheck(tla, cfg);
    	final LTS<Integer, String> lts = tlc.getLTSBuilder().toIncompleteDetAutIncludingAnErrorState();
    	
    	if (SafetyUtils.INSTANCE.ltsIsSafe(lts)) {
    		return "TRUE";
    	}
    	
		TLC tlcComp = new TLC();
		tlcComp.initialize(tlaAlphabetSpec, cfgAlphabetSpec);
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
		final String str = "one sig " + name + " extends " + ext + " {} {\n"
				+ "  lastIdx = " + strLastIdx + "\n"
				+ "  (" + strTrace + ") in path\n"
				+ "}";
		return str;
	}
	
	private static final String alloyFormlaInferJar = "/Users/idardik/Documents/CMU/compositional_ii/alsm-formula-synthesis/bin/alsm-formula-synthesis.jar";
	
	private static final String baseAlloyFormulaInfer = "open util/ordering[Idx]\n"
			+ "\n"
			+ "sig Var {}\n"
			+ "\n"
			+ "abstract sig Atom {}\n"
			+ "\n"
			+ "abstract sig Sort {\n"
			+ "	atoms : some Atom\n"
			+ "}\n"
			+ "\n"
			+ "// base name for an action\n"
			+ "abstract sig BaseName {\n"
			+ "	numParams : Int\n"
			+ "}\n"
			+ "\n"
			+ "// concrete action\n"
			+ "abstract sig Act {\n"
			+ "	baseName : one BaseName,\n"
			+ "	params : seq Atom\n"
			+ "}\n"
			+ "\n"
			+ "\n"
			+ "\n"
			+ "/* Formula signatures (represented by a DAG) */\n"
			+ "abstract sig Formula {\n"
			+ "	children : set Formula\n"
			+ "}\n"
			+ "\n"
			+ "sig TT, FF extends Formula {} {\n"
			+ "	no children\n"
			+ "}\n"
			+ "\n"
			+ "sig Not extends Formula {\n"
			+ "	child : Formula\n"
			+ "} {\n"
			+ "	children = child\n"
			+ "}\n"
			+ "\n"
			+ "sig Implies extends Formula {\n"
			+ "	left : Formula,\n"
			+ "	right : Formula\n"
			+ "} {\n"
			+ "	children = left + right\n"
			+ "}\n"
			+ "\n"
			+ "sig OnceVar extends Formula {\n"
			+ "	baseName : BaseName,\n"
			+ "	vars : seq Var\n"
			+ "} {\n"
			+ "	no children\n"
			+ "}\n"
			+ "\n"
			+ "sig Forall extends Formula {\n"
			+ "	var : Var,\n"
			+ "	sort : Sort,\n"
			+ "	matrix : Formula\n"
			+ "} {\n"
			+ "	children = matrix\n"
			+ "}\n"
			+ "\n"
			+ "sig Exists extends Formula {\n"
			+ "	var : Var,\n"
			+ "	sort : Sort,\n"
			+ "	matrix : Formula\n"
			+ "} {\n"
			+ "	children = matrix\n"
			+ "}\n"
			+ "\n"
			+ "one sig Root extends Formula {} {\n"
			+ "	one children\n"
			+ "}\n"
			+ "\n"
			+ "fact {\n"
			+ "	all f : Formula | f in Root.*children // all formulas must be a sub-formula of the root\n"
			+ "	no Root.^children & Root // root appears once\n"
			+ "	all f : Formula | f not in f.^children // eliminates cycles in formula nodes\n"
			+ "	all f1, f2 : Forall | (f2 in f1.^children) implies not (f1.var = f2.var) // do not quantify over a variable that's already in scope\n"
			+ "	OnceVar.vars.elems in Forall.var // approximately: no free variables\n"
			+ "	all f : OnceVar | #(f.vars) = f.baseName.numParams // the number of params in each action must match the action\n"
			+ "}\n"
			+ "\n"
			+ "\n"
			+ "sig Env {\n"
			+ "	maps : set(Var -> Atom)\n"
			+ "}\n"
			+ "one sig EmptyEnv extends Env {} {\n"
			+ "	no maps\n"
			+ "}\n"
			+ "\n"
			+ "abstract sig Idx {}\n"
			+ "\n"
			+ "abstract sig Trace {\n"
			+ "	path : Idx -> Act, // the path for the trace\n"
			+ "	lastIdx : Idx, // the last index in the path for the trace\n"
			+ "	satisfies : Env -> Idx -> Formula // formulas that satisfy this trace\n"
			+ "} {\n"
			+ "	// trace semantics, i.e. e |- t,i |= f, where e is an environment, t is a trace, i is an index, and f is a formula\n"
			+ "	all e : Env, i : Idx, f : TT | e->i->f in satisfies\n"
			+ "	all e : Env, i : Idx, f : FF | e->i->f not in satisfies\n"
			+ "	all e : Env, i : Idx, f : Not | e->i->f in satisfies iff (e->i->f.child not in satisfies)\n"
			+ "	all e : Env, i : Idx, f : Implies | e->i->f in satisfies iff (e->i->f.left in satisfies implies e->i->f.right in satisfies)\n"
			+ "	all e : Env, i : Idx, f : OnceVar | e->i->f in satisfies iff\n"
			+ "		((some a : Act | concreteAct[a,e,f] and i->a in path) or (some i' : Idx | i'->i in next and e->i'->f in satisfies))\n"
			+ "	all e : Env, i : Idx, f : Forall | e->i->f in satisfies iff\n"
			+ "		(all x : f.sort.atoms | some e' : Env | pushEnv[e',e,f.var,x] and e'->i->f.matrix in satisfies)\n"
			+ "	all e : Env, i : Idx, f : Exists | e->i->f in satisfies iff\n"
			+ "		(some x : f.sort.atoms | some e' : Env | pushEnv[e',e,f.var,x] and e'->i->f.matrix in satisfies)\n"
			+ "	all e : Env, i : Idx, f : Root | e->i->f in satisfies iff e->i->f.children in satisfies\n"
			+ "\n"
			+ "	// rule: only one action can happen at a given index\n"
			+ "	all a1, a2 : Act, i : Idx | (i->a1 in path and i->a2 in path) implies a1 = a2\n"
			+ "\n"
			+ "	// rule: maps (in each environment) is a function\n"
			+ "	all e : Env, v : Var, s,t : Atom | (v->s in e.maps and v->t in e.maps) implies s = t\n"
			+ "}\n"
			+ "\n"
			+ "pred concreteAct[a : Act, e : Env, f : OnceVar] {\n"
			+ "	f.baseName = a.baseName and\n"
			+ "	all j : (f.vars.inds + a.params.inds) |\n"
			+ "		let m = f.vars[j]->a.params[j] | some m and m in e.maps\n"
			+ "}\n"
			+ "\n"
			+ "pred pushEnv[env', env : Env, v : Var, x : Atom] {\n"
			+ "	env'.maps = env.maps + (v->x)\n"
			+ "}\n"
			+ "\n"
			+ "fun indices[t : Trace] : set Idx {\n"
			+ "	{ i : Idx | t.lastIdx in i.*next }\n"
			+ "}\n"
			+ "\n"
			+ "abstract sig PosTrace extends Trace {} {}\n"
			+ "abstract sig NegTrace extends Trace {} {}\n"
			+ "\n"
			+ "\n"
			+ "/* main */\n"
			+ "run {\n"
			+ "	// find a formula that separates \"good\" traces from \"bad\" ones\n"
			+ "	all pt : PosTrace | EmptyEnv->indices[pt]->Root in pt.satisfies\n"
			+ "	all nt : NegTrace | EmptyEnv->nt.lastIdx->Root not in nt.satisfies\n"
			+ "	minsome children // smallest formula possible\n"
			+ "} for 7 Formula,\n"
			+ "2 Var, 5 Env, 1 seq\n"
			+ "\n"
			+ "\n"
			+ "\n"
			+ "/* example traces */\n"
			+ "\n"
			+ "one sig rm1, rm2 extends Atom {}\n"
			+ "one sig RMs extends Sort {} {\n"
			+ "	atoms = rm1 + rm2\n"
			+ "}\n"
			+ "\n"
			+ "one sig SndPrepare extends BaseName {} {\n"
			+ "	numParams = 1\n"
			+ "}\n"
			+ "one sig RcvCommit extends BaseName {} {\n"
			+ "	numParams = 1\n"
			+ "}\n"
			+ "one sig RcvAbort extends BaseName {} {\n"
			+ "	numParams = 1\n"
			+ "}\n"
			+ "one sig SilentAbort extends BaseName {} {\n"
			+ "	numParams = 1\n"
			+ "}\n"
			+ "\n"
			+ "one sig SndPreparerm1 extends Act {} {\n"
			+ "	baseName = SndPrepare\n"
			+ "	params.first = rm1\n"
			+ "	#params = 1\n"
			+ "}\n"
			+ "one sig SndPreparerm2 extends Act {} {\n"
			+ "	baseName = SndPrepare\n"
			+ "	params.first = rm2\n"
			+ "	#params = 1\n"
			+ "}\n"
			+ "one sig RcvCommitrm1 extends Act {} {\n"
			+ "	baseName = RcvCommit\n"
			+ "	params.first = rm1\n"
			+ "	#params = 1\n"
			+ "}\n"
			+ "one sig RcvCommitrm2 extends Act {} {\n"
			+ "	baseName = RcvCommit\n"
			+ "	params.first = rm2\n"
			+ "	#params = 1\n"
			+ "}\n"
			+ "one sig RcvAbortrm1 extends Act {} {\n"
			+ "	baseName = RcvAbort\n"
			+ "	params.first = rm1\n"
			+ "	#params = 1\n"
			+ "}\n"
			+ "one sig RcvAbortrm2 extends Act {} {\n"
			+ "	baseName = RcvAbort\n"
			+ "	params.first = rm2\n"
			+ "	#params = 1\n"
			+ "}\n"
			+ "one sig SilentAbortrm1 extends Act {} {\n"
			+ "	baseName = SilentAbort\n"
			+ "	params.first = rm1\n"
			+ "	#params = 1\n"
			+ "}\n"
			+ "one sig SilentAbortrm2 extends Act {} {\n"
			+ "	baseName = SilentAbort\n"
			+ "	params.first = rm2\n"
			+ "	#params = 1\n"
			+ "}\n"
			+ "\n"
			+ "\n"
			+ "one sig T0, T1, T2, T3 extends Idx {}\n"
			+ "fact {\n"
			+ "	first = T0\n"
			+ "	next = T0->T1 + T1->T2 + T2->T3\n"
			+ "}\n"
			+ "";
}
