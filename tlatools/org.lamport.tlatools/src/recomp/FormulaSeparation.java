package recomp;

import java.io.BufferedReader;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import cmu.isr.ts.LTS;
import cmu.isr.ts.lts.RandTraceUtils;
import cmu.isr.ts.lts.SafetyUtils;
import lts.SymbolTable;
import net.automatalib.words.Word;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpDefNode;
import tlc2.TLC;
import tlc2.Utils;
import tlc2.tool.impl.FastTool;

public class FormulaSeparation {
	private final String tlaSys;
	private final String cfgSys;
	private final String tlaComp;
	private final String cfgComp;
	private final boolean usePropFile;
	private final String propFile;
	private final TLC tlcSys;
	private final TLC tlcComp;
	private final Set<String> internalActions;
	private final Map<String, List<String>> actionParamTypes;
	private final int maxActParamLen;
	private final Set<String> qvars;
	private final boolean verbose;
	
	public FormulaSeparation(final String tlaSys, final String cfgSys, final String tlaComp, final String cfgComp,
			final String propFile, final List<Utils.Pair<String,String>> otherComponents) {
		this.tlaSys = tlaSys;
		this.cfgSys = cfgSys;
		this.tlaComp = tlaComp;
		this.cfgComp = cfgComp;
		
		this.usePropFile = !propFile.equals("none");
		this.propFile = propFile;
		
		// TODO bound model checking to, say, 1 mil states
		tlcSys = new TLC();
    	tlcSys.modelCheck(tlaSys, cfgSys);
		tlcComp = new TLC();
    	tlcComp.initialize(tlaComp, cfgComp);
    	
    	final Set<String> otherComponentActs = otherComponents
    			.stream()
    			.map(p -> {
    				TLC tlc = new TLC();
    				tlc.initialize(p.first, p.second);
    				return tlc.actionsInSpec();
    			})
    			.reduce((Set<String>)new HashSet<String>(),
    					(acc,s) -> Utils.union(acc, s),
    					(s1,s2) -> Utils.union(s1, s2));
    	internalActions = Utils.setMinus(tlcComp.actionsInSpec(), otherComponentActs);
		
		// obtain a map of: action -> List(param type)
    	FastTool ft = (FastTool) tlcSys.tool;
		actionParamTypes = TLC.getTransitionRelationNode(ft, tlcSys, "Next").actionParamTypes(tlcSys.actionsInSpec());
		maxActParamLen = actionParamTypes.values()
				.stream()
				.mapToInt(l -> l.size())
				.max()
				.getAsInt();
		
		// TODO make the number of vars a param
		final int numParams = 2;
		qvars = IntStream.range(0, numParams)
				.mapToObj(i -> "var" + i)
				.collect(Collectors.toSet());
		
		verbose = false;
	}
	
	public String synthesizeSepInvariant() {
    	// config for producing positive traces
    	final String strCfgConstants = String.join("\n", tlcSys.tool.getModelConfig().getRawConstants());
    	final String cfgPosTraces = "pos_traces.cfg";
    	Utils.writeFile(cfgPosTraces, "SPECIFICATION Spec\nINVARIANT CandSep\n" + strCfgConstants);
    	
    	// config for producing negative traces
    	final String cfgNegTraces = "neg_traces.cfg";
    	final String negTracesSafety = this.usePropFile ? "\nINVARIANT Safety" : "";
    	Utils.writeFile(cfgNegTraces, String.join("\n", Utils.fileContents(cfgComp)) + negTracesSafety);
    	
    	//final List<String> rawComponents = Decomposition.decompAll(tla, cfg);
    	//final List<String> components = Composition.symbolicCompose(tla, cfg, "CUSTOM", "recomp_map.csv", rawComponents);
    	
    	/*final String initPosTrace = "one sig PT1 extends PosTrace {} {\n"
    			+ "	 lastIdx = T3\n"
    			+ "	 (T0->SndPreparerm1 + T1->SndPreparerm2 + T2->RcvCommitrm2 + T3->RcvCommitrm1) in path\n"
    			+ "}";*/
    	// TODO make the init trace len a param
    	final Word<String> initTrace = RandTraceUtils.INSTANCE.randTrace(tlcSys.getLTSBuilder().toIncompleteDetAutWithoutAnErrorState(), 8);
    	final String initPosTrace = createAlloyTrace(initTrace, "PT1", "PosTrace");
    	List<String> posTraces = new ArrayList<>();
    	posTraces.add(initPosTrace);
    	
    	List<String> invariants = new ArrayList<>();
    	boolean formulaSeparates = false;
    	
    	int round = 1;
    	while (!formulaSeparates) {
    		System.out.println("Round " + round);
    		
    		// generate a negative trace for this round; we will generate a formula (assumption) that eliminates
    		// the negative trace
    		final String invariant = prettyConjuncts(invariants);
        	final String tlaCompHV = writeHistVarsSpec(tlaComp, cfgComp, invariant, true);
        	final String negTrace = isCandSepInvariant(tlaCompHV, cfgNegTraces, "NT", "NegTrace");
    		formulaSeparates = negTrace.equals("TRUE");
    		Utils.printVerbose(verbose, "negTrace:\n" + negTrace);

    		// use the negative trace and all existing positive traces to generate a formula
			// keep generating positive traces until the formula turns into an invariant
    		boolean isInvariant = false;
    		while (!formulaSeparates && !isInvariant) {
    			final String formula = synthesizeFormula(negTrace, posTraces);
    			
    			// generate positive traces until the formula becomes an invariant
    			final int ptNum = posTraces.size() + 1;
    			final String ptName = "PT" + ptNum;
    	    	final String tlaSysHV = writeHistVarsSpec(tlaSys, cfgSys, formula, false);
    			final String posTrace = isCandSepInvariant(tlaSysHV, cfgPosTraces, ptName, "PosTrace");
    			isInvariant = posTrace.equals("TRUE");
    			
    			System.out.println("Synthesized: " + formula);
    			if (isInvariant) {
    				invariants.add(formula);
    				System.out.println("The formula is an invariant! Moving to the next round.");
    			}
    			else {
    	    		Utils.printVerbose(verbose, "posTrace:\n" + posTrace);
    				posTraces.add(posTrace);
    			}
    		}
    		++round;
			System.out.println();
    	}
    	
    	return prettyConjuncts(invariants);
	}
	
	private String isCandSepInvariant(final String tla, final String cfg, final String name, final String ext) {
    	TLC tlc = new TLC();
    	tlc.modelCheck(tla, cfg);
    	final LTS<Integer, String> lts = tlc.getLTSBuilder().toIncompleteDetAutIncludingAnErrorState();
    	
    	if (SafetyUtils.INSTANCE.ltsIsSafe(lts)) {
    		return "TRUE";
    	}
		
		// if candSep isn't an invariant, return a trace that should be covered by the formula
		return createAlloyTrace(SafetyUtils.INSTANCE.findErrorTrace(lts), name, ext);
	}
	
	private String createAlloyTrace(final Word<String> word, final String name, final String ext) {
		// use the alphabet for the component
		final Set<String> alphabet = this.tlcComp.actionsInSpec();
		
		final List<String> trace = word
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
	
	private String synthesizeFormula(final String negTrace, final List<String> posTraces) {
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
		
		return formulaBuilder.toString();
	}
	
	private void writeAlloyFormulaInferFile(final String fileName, final String negTrace, final List<String> posTraces) {
		// add all atoms, i.e. the values in each constant
		final Set<String> allAtoms = tlcSys.tool.getModelConfig().getConstantsAsList()
				.stream()
				.filter(l -> l.size() == 2) // only retain assignments
				.map(l -> l.get(1)) // only retain the values of each assignment (i.e. the set of atoms)
				.map(s -> s.replaceAll("[{}]", "").split(",")) // each element in the stream is now an array of atoms
				.reduce((Set<String>)new HashSet<String>(),
						(acc,l) -> Utils.union(acc, Utils.toSet(l)),
						(l1,l2) -> Utils.union(l1,l2))
				.stream()
				.map(s -> s.trim())
				.collect(Collectors.toSet());
		final String strAtomList = String.join(", ", allAtoms);
		final String atomsDecl = "one sig " + strAtomList + " extends Atom {}";
		
		// create a map of sort -> elements (elements = atoms)
		Map<String, Set<String>> sortElements = new HashMap<>();
		for (final List<String> constList : tlcSys.tool.getModelConfig().getConstantsAsList()) {
			if (constList.size() == 2) {
				// constList is a CONSTANT assignment
				final String sort = constList.get(0);
				final Set<String> elems = Utils.toArrayList(constList.get(1).replaceAll("[{}]", "").split(","))
						.stream() // each element in the stream is an array of elements (atoms)
						.map(e -> e.trim())
						.collect(Collectors.toSet());
				sortElements.put(sort, elems);
			}
		}
		
		// define each sort as the set of its elements (elements = atoms)
		final String strSortDecls = sortElements.keySet()
				.stream()
				.map(sort -> {
					final Set<String> elems = sortElements.get(sort);
					final String atoms = String.join(" + ", elems);
					final String decl = "one sig " + sort + " extends Sort {} {\n"
							+ "	atoms = " + atoms + "\n"
							+ "}";
					return decl;
				})
				.collect(Collectors.joining("\n"));
		
		// define each concrete action (and its base name) in the component
		StringBuilder concActsBuilder = new StringBuilder();
		for (final String act : this.tlcComp.actionsInSpec()) {
			final List<String> paramTypes = this.actionParamTypes.get(act);
			final String strBaseDecl = "one sig " + act + " extends BaseName {} {\n"
					+ "	numParams = " + paramTypes.size() + "\n"
					+ "}";
			
			Set<List<String>> concreteActionParams = new HashSet<>();
			concreteActionParams.add(new ArrayList<>());
			for (final String paramType : paramTypes) {
				// type = sort
				concreteActionParams = cartProduct(concreteActionParams, sortElements.get(paramType));
			}
			
			final String strConcreteActions = concreteActionParams
					.stream()
					.map(params -> {
						final String concActName = act + String.join("", params);
						StringBuilder paramsBuilder = new StringBuilder();
						for (int i = 0; i < params.size(); ++i) {
							final String param = params.get(i);
							paramsBuilder.append("	params[").append(i).append("] = ").append(param).append("\n");
						}
						final String numParams = "	#params = " + params.size() + "\n";
						return "one sig " + concActName + " extends Act {} {\n"
								+ "	baseName = " + act + "\n"
								+ paramsBuilder.toString()
								+ numParams
								+ "}";
					})
					.collect(Collectors.joining("\n"));
			
			concActsBuilder.append(strBaseDecl).append("\n").append(strConcreteActions).append("\n\n");
		}
		
		// determine the max length of the traces
		final int maxTraceLen = Utils.union(posTraces.stream().collect(Collectors.toSet()), Utils.setOf(negTrace))
				.stream()
				.map(t -> Utils.toSet(t.split("\n")))
				.reduce((Set<String>)new HashSet<String>(),
						(acc,s) -> Utils.union(acc, s),
						(s1,s2) -> Utils.union(s1, s2))
				.stream()
				.filter(l -> l.contains("lastIdx = T"))
				.map(s -> s.replace("lastIdx = T", "").trim())
				.mapToInt(s -> Integer.parseInt(s))
				.max()
				.getAsInt();
		
		// create the indices that are needed for the traces
		final String strIndices = IntStream.range(0, maxTraceLen+1)
				.mapToObj(i -> "T" + i)
				.collect(Collectors.joining(", "));
		final String strIndicesDecl = "one sig " + strIndices + " extends Idx {}";
		
		final String strIndicesNext = IntStream.range(0, maxTraceLen)
				.mapToObj(i -> "T"+i + "->T"+(i+1))
				.collect(Collectors.joining(" + "));
		final String strInternalActs = this.internalActions
				.stream()
				.map(act -> "	no OnceVar.baseName & " + act)
				.collect(Collectors.joining("\n"));
		final String strIndicesFacts = "fact {\n"
				+ "	first = T0\n"
				+ "	next = " + strIndicesNext + "\n"
				+ strInternalActs + "\n"
				+ "}";
		
		// declare the quantifier variables
		final String qvarDelc = "one sig " + String.join(", ", this.qvars) + " extends Var {} {}";
		
		// create all possible environments
		final String strNonEmptyEnvs = allEnvs(this.qvars, allAtoms)
				.stream()
				.map(env -> {
					final String name = env.stream().map(m -> m.first + "to" + m.second).collect(Collectors.joining());
					final String maps = env.stream().map(m -> m.first + "->" + m.second).collect(Collectors.joining(" + "));
					return "one sig " + name + " extends Env {} {\n"
						+ "	maps = " + maps + "\n"
						+ "}";
				})
				.collect(Collectors.joining("\n"));
		
		final String alloyFormulaInfer = baseAlloyFormulaInfer
				+ maxActParamLen + " seq\n"
				+ "\n" + atomsDecl + "\n"
				+ "\n" + strSortDecls + "\n"
				+ "\n" + concActsBuilder.toString()
				+ "\n" + strIndicesDecl + "\n"
				+ "\n" + strIndicesFacts + "\n\n"
				+ "\n" + qvarDelc + "\n\n"
				+ "\n" + strNonEmptyEnvs + "\n\n"
				+ "\n" + negTrace + "\n\n"
				+ String.join("\n", posTraces) + "\n";
		Utils.writeFile(fileName, alloyFormulaInfer);
	}
	
	private String writeHistVarsSpec(final String tla, final String cfg, final String candSep, boolean candSepInActions) {
    	final String tlaCompBaseName = tla.replaceAll("\\.tla", "");
    	final String specName = tlaCompBaseName + "_hist";
    	
		TLC tlc = new TLC();
		tlc.initialize(tla, cfg);

    	final FastTool ft = (FastTool) tlc.tool;
		final String moduleName = tlc.getModelName();
		final ModuleNode mn = ft.getModule(moduleName);
		final List<OpDefNode> moduleNodes = Utils.toArrayList(mn.getOpDefs())
				.stream()
				// only retain module for the .tla file
				.filter(d -> moduleName.equals(d.getOriginallyDefinedInModuleNode().getName().toString()))
				.filter(d -> !d.getName().toString().equals("vars")) // remove the vars decl; we insert this manually
				.collect(Collectors.toList());
		
		// create the history vars that represent "once(action)"
		final Set<String> onceVars = tlc.actionsInSpec()
				.stream()
				.map(v -> "once" + v)
				.collect(Collectors.toSet());
		
		List<String> strModuleNodes = moduleNodes
				.stream()
				.map(d -> {
					final String dname = d.getName().toString();
					if (tlc.actionsInSpec().contains(dname)) {
						d.addOnceVars(onceVars,candSepInActions);
					}
					else if (dname.equals("Init")) {
						d.addOnceInitVars(onceVars, actionParamTypes);
					}
					return d;
				 })
				.map(d -> d.toTLA())
				.collect(Collectors.toList());
		
		// add CandSep to the module definitions (after any dependencies, where a dependency
		// is a definition for a type symbol that occurs in CandSep)
		final Set<String> allTypes = actionParamTypes
				.values()
				.stream()
				.reduce((Set<String>)new HashSet<String>(),
						(acc,l) -> Utils.union(acc, l.stream().collect(Collectors.toSet())),
						(l1,l2) -> Utils.union(l1,l2));
		
		Set<OpDefNode> candSepDependencyNodes = moduleNodes
				.stream()
				.filter(d -> allTypes.contains(d.getName().toString()))
				.collect(Collectors.toSet());
		
		for (int i = 0; i < moduleNodes.size(); ++i) {
			final OpDefNode defNode = moduleNodes.get(i);
			if (candSepDependencyNodes.isEmpty()) {
				strModuleNodes.add(i, "CandSep ==\n" + candSep);
				break;
			}
			else if (candSepDependencyNodes.contains(defNode)) {
				candSepDependencyNodes.remove(defNode);
			}
			Utils.assertTrue(i < moduleNodes.size()-1, "Could not find a place for CandSep!");
		}
		
		// add the safety property in (if one is provided)
		// only include the safety property when writing negative traces, i.e. when candSepInActions is true
		final String safetyDecl = !(this.usePropFile && candSepInActions) ? "" :
			"\nSafety ==\n" + String.join("\n", Utils.fileContents(this.propFile)) + "\n";
		
		// construct the spec
		final String specBody = String.join("\n\n", strModuleNodes);
		
        final String specDecl = "--------------------------- MODULE " + specName + " ---------------------------";
        final String endModule = "=============================================================================";
        
        final List<String> moduleWhiteList =
        		Arrays.asList("Bags", "FiniteSets", "Functions", "Integers", "Json", "Naturals",
        				"NaturalsInduction", "RealTime", "Sequences", "SequencesExt", "TLC", "TLCExt");
        ArrayList<String> moduleNameList = Utils.filterArrayWhiteList(moduleWhiteList, ft.getModuleNames());

        final String moduleList = String.join(", ", moduleNameList);
        final String constantsDecl = tlc.constantsInSpec().isEmpty() ? "" : "CONSTANTS " + String.join(", ", tlc.constantsInSpec());
        final String varList = String.join(", ", Utils.union(tlc.stateVarsInSpec(), onceVars));
        final String modulesDecl = moduleList.isEmpty() ? "" : "EXTENDS " + moduleList;
        final String varsDecl = "VARIABLES " + varList;
        final String varsListDecl = "vars == <<" + varList + ">>";
        
        StringBuilder builder = new StringBuilder();
        builder.append(specDecl).append("\n");
        builder.append(modulesDecl).append("\n");
        builder.append("\n");
        builder.append(constantsDecl).append("\n");
        builder.append("\n");
        builder.append(varsDecl).append("\n");
        builder.append("\n");
        builder.append(varsListDecl).append("\n");
        builder.append("\n");
        builder.append(specBody);
        builder.append("\n");
        builder.append(safetyDecl);
        builder.append(endModule).append("\n");

        final String fileName = specName + ".tla";
        final String file = fileName;
        Utils.writeFile(file, builder.toString());
        
        return specName;
	}

	private static Set<Set<Utils.Pair<String,String>>> allEnvs(final Set<String> vars, final Set<String> atoms) {
		// don't include the empty env
		Set<Set<Utils.Pair<String,String>>> envs = allEnvs(vars, atoms, new HashSet<>());
		envs.remove(new HashSet<>());
		return envs;
	}
	
	private static Set<Set<Utils.Pair<String,String>>> allEnvs(final Set<String> vars, final Set<String> atoms, Set<Utils.Pair<String,String>> env) {
		Set<Set<Utils.Pair<String,String>>> rv = new HashSet<>();
		rv.add(env);
		for (final String v : vars) {
			for (final String a : atoms) {
				final Utils.Pair<String,String> newMap = new Utils.Pair<>(v, a);
				final Set<Set<Utils.Pair<String,String>>> envsFromNewMap =
						allEnvs(Utils.setMinus(vars,Set.of(v)), atoms, Utils.union(env,Set.of(newMap)));
				final Set<Set<Utils.Pair<String,String>>> envsWithoutTheMap =
						allEnvs(Utils.setMinus(vars,Set.of(v)), atoms, env);
				rv.addAll(envsFromNewMap);
				rv.addAll(envsWithoutTheMap);
			}
		}
		return rv;
	}
	
	private static String prettyConjuncts(final List<String> conjuncts) {
		if (conjuncts.isEmpty()) {
			return "TRUE";
		}
		final String delim = "\n/\\ ";
		return "/\\ " + String.join(delim, conjuncts);
	}
	
	private static Set<List<String>> cartProduct(final Set<List<String>> acc, final Set<String> s) {
		Set<List<String>> product = new HashSet<>();
		for (final List<String> acce : acc) {
			for (final String se : s) {
				List<String> l = new ArrayList<>(acce);
				l.add(se);
				product.add(l);
			}
		}
		return product;
	}
	
	// TODO fix path
	private static final String alloyFormlaInferJar = "/Users/idardik/Documents/CMU/compositional_ii/alsm-formula-synthesis/bin/alsm-formula-synthesis.jar";
	
	private static final String baseAlloyFormulaInfer = "open util/ordering[Idx]\n"
			+ "\n"
			+ "abstract sig Var {}\n"
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
			+ "	OnceVar.vars.elems in (Forall.var + Exists.var) // approximately: no free variables\n"
			+ "	all f : OnceVar | #(f.vars) = f.baseName.numParams // the number of params in each action must match the action\n"
			+ "\n"
			+ "	// do not quantify over a variable that's already in scope\n"
			+ "	all f1, f2 : Forall | (f2 in f1.^children) implies not (f1.var = f2.var)\n"
			+ "	all f1, f2 : Exists | (f2 in f1.^children) implies not (f1.var = f2.var)\n"
			+ "	all f1 : Forall, f2 : Exists | (f2 in f1.^children) implies not (f1.var = f2.var)\n"
			+ "	all f1 : Exists, f2 : Forall | (f2 in f1.^children) implies not (f1.var = f2.var)\n"
			+ "}\n"
			+ "\n"
			+ "\n"
			+ "abstract sig Env {\n"
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
			+ "one sig EmptyTrace extends Trace {} {\n"
			+ "	 no path\n"
			+ "}\n"
			+ "\n"
			+ "\n"
			+ "/* main */\n"
			+ "run {\n"
			+ "	// find a formula that separates \"good\" traces from \"bad\" ones\n"
			+ "	all pt : PosTrace | EmptyEnv->indices[pt]->Root in pt.satisfies\n"
			+ "	all nt : NegTrace | EmptyEnv->nt.lastIdx->Root not in nt.satisfies\n"
			+ "	EmptyEnv->T0->Root in EmptyTrace.satisfies\n"
			+ "	minsome children // smallest formula possible\n"
			// TODO make the formula len a param
			+ "} for 7 Formula,\n";
}
