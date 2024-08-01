package tlc2;

import java.util.List;

import recomp.Composition;
import recomp.Decomposition;
import recomp.RecompVerify;

public class Main {
    public static void main(String[] args) throws Exception {
    	try {
    		calc(args);
		}
    	catch (Exception e) {
    		e.printStackTrace();
    	}
    	finally {
    		System.exit(0);
    	}
    }
    
    public static void calc(String[] args) {
    	if (args.length >= 2) {
    		final String tla = args[0];
    		final String cfg = args[1];
    		final boolean decompose = hasFlag(args, "--decomp");
    		
    		if (decompose) {
    			// write a config without any invariants / properties
    	    	final String noInvsCfg = "no_invs.cfg";
    	    	Utils.writeFile(noInvsCfg, "SPECIFICATION Spec");
    	    	
    			// only decompose the spec. this is primarily used as pre-processing for the parallel algorithm
    			final List<String> components = Decomposition.decompAll(tla, cfg);
    			final List<String> trimmedComponents = Composition.orderedTrimmedComponents(tla, cfg, components);
    		 	System.out.println(String.join(",", trimmedComponents));
    		}
    		else {
    			// run recomp-verify
        		final boolean verbose = hasFlag(args, "--verbose");
        		final boolean custom = hasFlag(args, "--cust");
        		final boolean naive = hasFlag(args, "--naive");
				final boolean parallel = hasFlag(args, "--parallel");
				//final boolean heuristic = !custom && !naive;
        		final String recompFile = custom ? positionalArg(args, "--cust") : "";
        		
        		// TODO ian this is lazy
        		Utils.assertTrue(!custom || !recompFile.isEmpty(), "--cust must be followed by a recomp file!");
        		Utils.assertTrue(!(custom && naive), "--custom and --naive are mutually exclusive options!");
        		
        		final String recompStrategy = custom ? "CUSTOM" : naive ? "NAIVE" : "HEURISTIC";

				if (parallel) {
					System.out.println("Parallel compilation");
					RecompVerify.runRecompVerify(tla, cfg, "parallel", recompFile, verbose);
				} else {
					RecompVerify.runRecompVerify(tla, cfg, recompStrategy, recompFile, verbose);
				}
    		}
    	}
    	
    	// invalid args, display usage
    	else {
    		System.out.println("usage1: recomp-verify <spec> <cfg> [--naive] [--cust <recomp-file>] [--verbose]\n"
    				+ "usage2: recomp-verify <spec> <cfg> --decomp\n"
    				+ "* in usage1: --naive and --cust are mutually exclusive");
    	}

    }
    
    private static boolean hasFlag(String[] args, final String flag) {
    	return Utils.toArrayList(args)
				.stream()
				.filter(s -> s.equals(flag))
				.count() > 0;
    }
    
    private static String positionalArg(String[] args, final String param) {
    	int paramIdx = -1;
    	for (int i = 0; i < args.length; ++i) {
    		if (param.endsWith(args[i])) {
    			// the positional arg is right after the param flag
    			paramIdx = i + 1;
    		}
    	}
    	Utils.assertTrue(paramIdx >= 0 && paramIdx < args.length, "Invalid use of the param flag: " + param);
    	return args[paramIdx];
    }
}
