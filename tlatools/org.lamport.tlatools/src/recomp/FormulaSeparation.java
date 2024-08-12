package recomp;

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
	private final Map<String, Set<String>> sortElementsMap;
	private final Map<String, List<String>> actionParamTypes;
	private final int maxActParamLen;
	private final int maxNumVarsPerType;
	private final Set<String> qvars;
	private final Set<Set<String>> legalEnvVarCombos;
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
    	
    	// obtain a map of: sort -> Set(elements/atoms in the sort)
    	sortElementsMap = createSortElementsMap(tlcSys);
		
		// obtain a map of: action -> List(param type)
    	FastTool ft = (FastTool) tlcSys.tool;
		actionParamTypes = TLC.getTransitionRelationNode(ft, tlcSys, "Next").actionParamTypes(tlcSys.actionsInSpec());
		maxActParamLen = actionParamTypes.values()
				.stream()
				.mapToInt(l -> l.size())
				.max()
				.getAsInt();

		maxNumVarsPerType = 2; // TODO make this a param
		final int maxNumVars = 3; // TODO make the number of vars a param
		final int numTypes = sortElementsMap.keySet().size();
		final int numVars = Math.min(maxNumVars, maxNumVarsPerType*numTypes);
		final String varNameBase = "var";
		qvars = IntStream.range(0, numVars)
				.mapToObj(i -> varNameBase + i)
				.collect(Collectors.toSet());
		
		legalEnvVarCombos = IntStream.range(0, numVars)
				.mapToObj(i ->
					IntStream.range(0, i+1)
						.mapToObj(j -> varNameBase + j)
						.collect(Collectors.toSet()))
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
    	final int initTraceLen = 4;
    	final Word<String> initTrace = RandTraceUtils.INSTANCE.randTrace(tlcSys.getLTSBuilder().toIncompleteDetAutWithoutAnErrorState(), initTraceLen);
    	final AlloyTrace initPosTrace = createAlloyTrace(initTrace, "PT1", "PosTrace");
    	List<AlloyTrace> posTraces = new ArrayList<>();
    	posTraces.add(initPosTrace);
    	
    	List<Formula> invariants = new ArrayList<>();
    	boolean formulaSeparates = false;
    	
    	int round = 1;
    	while (!formulaSeparates) {
    		System.out.println("Round " + round);
    		PerfTimer timer = new PerfTimer();
    		
    		// generate a negative trace for this round; we will generate a formula (assumption) that eliminates
    		// the negative trace
    		final Formula invariant = Formula.conjunction(invariants);
        	final String tlaCompHV = writeHistVarsSpec(tlaComp, cfgComp, invariant, true);
        	final AlloyTrace negTrace = isCandSepInvariant(tlaCompHV, cfgNegTraces, "NT", "NegTrace");
    		formulaSeparates = !negTrace.hasError();
    		Utils.printVerbose(verbose, "negTrace:\n" + negTrace.fullSigString());

    		// use the negative trace and all existing positive traces to generate a formula
			// keep generating positive traces until the formula turns into an invariant
    		boolean isInvariant = false;
    		while (!formulaSeparates && !isInvariant) {
    			final Formula formula = synthesizeFormula(negTrace, posTraces, invariant.getNumFluents());
    			
    			// if the latest constraints are unsatisfiable then stop and report this to the user
    			if (formula.isUNSAT()) {
    				if (invariants.isEmpty()) {
    					return "UNSAT";
    				}
    				return Formula.conjunction(invariants).getFormula();
    			}
    			
    			// generate positive traces until the formula becomes an invariant
    			final int ptNum = posTraces.size() + 1;
    			final String ptName = "PT" + ptNum;
    	    	final String tlaSysHV = writeHistVarsSpec(tlaSys, cfgSys, formula, false);
    			final AlloyTrace posTrace = isCandSepInvariant(tlaSysHV, cfgPosTraces, ptName, "PosTrace");
    			isInvariant = !posTrace.hasError();
    			
    			System.out.println("Synthesized: " + formula);
    			if (isInvariant) {
    				invariants.add(formula);
    				System.out.println("The formula is an invariant! Moving to the next round.");
    			}
    			else {
    	    		Utils.printVerbose(verbose, "posTrace:\n" + posTrace.fullSigString());
    				posTraces.add(posTrace);
    			}
    		}
    		System.out.println("Round " + round + " took " + timer.timeElapsedSeconds() + " seconds");
    		++round;
			System.out.println();
    	}
    	
    	return Formula.conjunction(invariants).getFormula();
	}
	
	private AlloyTrace isCandSepInvariant(final String tla, final String cfg, final String name, final String ext) {
    	TLC tlc = new TLC();
    	tlc.modelCheck(tla, cfg);
    	final LTS<Integer, String> lts = tlc.getLTSBuilder().toIncompleteDetAutIncludingAnErrorState();
    	
    	if (SafetyUtils.INSTANCE.ltsIsSafe(lts)) {
    		return new AlloyTrace();
    	}
		
		// if candSep isn't an invariant, return a trace that should be covered by the formula
		return createAlloyTrace(SafetyUtils.INSTANCE.findErrorTrace(lts), name, ext);
	}
	
	private AlloyTrace createAlloyTrace(final Word<String> word, final String name, final String ext) {
		// use the alphabet for the component
		final Set<String> alphabet = this.tlcComp.actionsInSpec();
		
		final List<String> trace = word
				.stream()
				.filter(act -> {
					final String abstractAct = act.replaceAll("\\..*$", "");
					return alphabet.contains(abstractAct);
				})
				.collect(Collectors.toList());
		
		final int lastIdx = trace.size() - 1;
		final String alloyLastIdx = "T" + lastIdx;
		final String path = IntStream.range(0, trace.size())
				.mapToObj(i -> {
					final String time = "T" + i;
					final String act = trace.get(i).replace(".", "");
					return time + "->" + act;
				})
				.collect(Collectors.joining(" + "));
		final String pathParens = "(" + path + ")";
		
		return new AlloyTrace(name, ext, lastIdx, alloyLastIdx, pathParens);
	}
	
	private Formula synthesizeFormula(final AlloyTrace negTrace, final List<AlloyTrace> posTraces, final int curNumFluents) {
		// split inference into several jobs, where each job assigns possible types to variables
		// note: the variable orderings matter because of the legal environments we chose (see legalEnvVarCombos)
		// so we need to consider the order of vars, not just how many of each type
		final Set<String> allTypes = this.actionParamTypes.values()
				.stream()
				.map(l -> l.stream().collect(Collectors.toSet()))
				.reduce((Set<String>)new HashSet<String>(),
						(acc,s) -> Utils.union(acc, s),
						(s1,s2) -> Utils.union(s1, s2));
		
		final Set<Map<String,String>> envVarTypes = allEnvVarTypes(allTypes);
		Utils.assertTrue(!envVarTypes.isEmpty(), "internal error: envVarTypes is empty!");
		
		FormulaSynth formSynth = new FormulaSynth();
		return formSynth.synthesizeFormula(envVarTypes, negTrace, posTraces,
				tlcSys, tlcComp, internalActions, sortElementsMap, actionParamTypes, maxActParamLen,
				qvars, legalEnvVarCombos, curNumFluents);
	}
	
	private String writeHistVarsSpec(final String tla, final String cfg, final Formula candSep, boolean candSepInActions) {
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
		
		List<String> strModuleNodes = moduleNodes
				.stream()
				.map(d -> {
					final String dname = d.getName().toString();
					if (tlc.actionsInSpec().contains(dname)) {
						d.addFluentVars(candSep, candSepInActions);
					}
					else if (dname.equals("Init")) {
						d.addFluentInitVars(candSep); //, actionParamTypes);
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
				strModuleNodes.add(i, "CandSep ==\n" + candSep.getFormula());
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
        final String varList = String.join(", ", Utils.union(tlc.stateVarsInSpec(), candSep.getFluentVars()));
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
	
	
	/* Helper methods */
	
	private Set<Map<String,String>> allEnvVarTypes(final Set<String> allTypes) {
		return allEnvVarTypes(allTypes, new HashMap<>(), new HashMap<>());
	}
	
	private Set<Map<String,String>> allEnvVarTypes(final Set<String> allTypes, Map<String,String> envTypes,
			Map<String,Integer> envTypeCounts) {
		Set<Map<String,String>> cumEnvVarTypes = new HashSet<>();
		
		// base case
		final boolean allVarsAssigned = this.qvars
				.stream()
				.allMatch(v -> envTypes.containsKey(v)); // is v assigned a value?
		if (allVarsAssigned) {
			cumEnvVarTypes.add(envTypes);
			return cumEnvVarTypes;
		}
		
		for (final String type : allTypes) {
			final int numTimesTypeUsedInEnv = envTypeCounts.getOrDefault(type, 0);
			if (numTimesTypeUsedInEnv < maxNumVarsPerType) {
				// for each var that hasn't already been assigned a type, assign it to <type>
				final Set<String> unassignedVars = this.qvars
						.stream()
						.filter(v -> !envTypes.containsKey(v))
						.collect(Collectors.toSet());
				for (final String var : unassignedVars) {
					Map<String,String> newEnvTypes = new HashMap<>(envTypes);
					newEnvTypes.put(var, type);
					Map<String,Integer> newEnvTypeCounts = new HashMap<>(envTypeCounts);
					newEnvTypeCounts.put(type, numTimesTypeUsedInEnv+1);
					
					final Set<Map<String,String>> partialEnvVarTypes = allEnvVarTypes(allTypes, newEnvTypes, newEnvTypeCounts);
					cumEnvVarTypes.addAll(partialEnvVarTypes);
				}
			}
		}
		
		return cumEnvVarTypes;
	}
	
	private static Map<String, Set<String>> createSortElementsMap(TLC tlc) {
		// create a map of sort -> elements (elements = atoms)
		Map<String, Set<String>> sortElements = new HashMap<>();
		for (final List<String> constList : tlc.tool.getModelConfig().getConstantsAsList()) {
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
		return sortElements;
	}
}
