package recomp;

import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;

import tlc2.TLC;

public class FormulaSynth {
	private String globalFormula = "UNSAT";
	private final Lock lock = new ReentrantLock();
	private final Condition aWorkerIsDone = lock.newCondition();
	
	private Set<FormulaSynthWorker> workers;
	private ExecutorService threadPool;
	
	/**
	 * Manually synchronized
	 * @param formula
	 */
	public void setFormula(final String formula) {
		lock.lock();
		try {
			if (this.globalFormula.contains("UNSAT") && !formula.contains("UNSAT")) {
				this.globalFormula = formula;
				this.aWorkerIsDone.signalAll();
			}
		}
		finally {
			lock.unlock();
			
			// we clean up the workers in a this method so the workers get cleaned up in a separate thread
			// (the thread of the worker who finishes first)
			this.cleanUpWorkers();
		}
	}

	/**
	 * This methods is intended to be called exactly once.
	 * @return
	 */
	public String synthesizeFormula(Set<Map<String,String>> envVarTypes,
			AlloyTrace negTrace, List<AlloyTrace> posTraces,
			TLC tlcSys, TLC tlcComp, Set<String> internalActions,
			Map<String, Set<String>> sortElementsMap, Map<String, List<String>> actionParamTypes,
			int maxActParamLen, Set<String> qvars, Set<Set<String>> legalEnvVarCombos) {
		
		this.workers = new HashSet<>();
		int id = 0;
		for (final Map<String,String> m : envVarTypes) {
			final FormulaSynthWorker worker = new FormulaSynthWorker(this, m, id++, negTrace, posTraces,
					tlcSys, tlcComp, internalActions, sortElementsMap, actionParamTypes, maxActParamLen,
					qvars, legalEnvVarCombos);
			this.workers.add(worker);
		}
		
		final int maxNumThreads = 25;
		this.threadPool = Executors.newFixedThreadPool(maxNumThreads);
		for (FormulaSynthWorker worker : workers) {
			this.threadPool.submit(worker);
		}
		
		try {
			int numWorkersDone = 0;
			while (numWorkersDone < workers.size()) {
				lock.lock();
				try {
					aWorkerIsDone.await();
				} catch (InterruptedException e) {
					// we expect to be interrupted, so do nothing
				}
				++numWorkersDone;
				final String formula = this.globalFormula;
				if (!formula.contains("UNSAT")) {
					return formula;
				}
			}
		}
		finally {
			lock.unlock();
		}

		// if we reach this point it means that we could not synthesize a formula
		return "UNSAT";
	}
	
	private void cleanUpWorkers() {
		this.threadPool.shutdownNow();
		for (FormulaSynthWorker worker : this.workers) {
			worker.kill();
		}
	}
}
