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
	private static final int MAX_NUM_THREADS = 25;
	
	private String globalFormula = "{\"formula\":\"UNSAT\"}";
	private int winningWorkerId = -1;
	private double winningTimeElapsedInSeconds = 0.0;
	private final Lock lock = new ReentrantLock();
	private final Condition aWorkerIsDone = lock.newCondition();
	
	private Set<FormulaSynthWorker> workers;
	private ExecutorService threadPool;
	
	/**
	 * Manually synchronized
	 * @param formula
	 */
	public void setFormula(final String formula, int workerId, double timeElapsedInSeconds) {
		lock.lock();
		try {
			if (this.globalFormula.contains("UNSAT") && !formula.contains("UNSAT") && !formula.trim().isEmpty()) {
				this.globalFormula = formula;
				this.winningWorkerId = workerId;
				this.winningTimeElapsedInSeconds = timeElapsedInSeconds;
			}
			// no matter what, notify the master that this thread is done
			this.aWorkerIsDone.signalAll();
		}
		finally {
			lock.unlock();
		}
	}

	/**
	 * This method is intended to be called exactly once.
	 * @return
	 */
	public Formula synthesizeFormula(Set<Map<String,String>> envVarTypes,
			AlloyTrace negTrace, List<AlloyTrace> posTraces,
			TLC tlcSys, TLC tlcComp, Set<String> internalActions,
			Map<String, Set<String>> sortElementsMap, Map<String, List<String>> actionParamTypes,
			int maxActParamLen, Set<String> qvars, Set<Set<String>> legalEnvVarCombos,
			int curNumFluents) {
		
		PerfTimer timer = new PerfTimer();
		this.workers = new HashSet<>();
		int id = 0;
		for (final Map<String,String> m : envVarTypes) {
			final FormulaSynthWorker worker = new FormulaSynthWorker(this, m, id++, negTrace, posTraces,
					tlcSys, tlcComp, internalActions, sortElementsMap, actionParamTypes, maxActParamLen,
					qvars, legalEnvVarCombos, curNumFluents);
			this.workers.add(worker);
		}
		
		this.threadPool = Executors.newFixedThreadPool(MAX_NUM_THREADS);
		for (FormulaSynthWorker worker : workers) {
			this.threadPool.submit(worker);
		}
		
		try {
			int numWorkersDone = 0;
			while (numWorkersDone < workers.size()) {
				lock.lock();
				try {
					aWorkerIsDone.await();
				}
				catch (InterruptedException e) {}
				++numWorkersDone;
				final Formula formula = new Formula(this.globalFormula, this.winningWorkerId);
				if (!formula.isUNSAT()) {
					System.out.println("Formula synthesis info:\n"
							+ "  overall (multithread) time: " + timer.timeElapsedSeconds() + " seconds\n"
							+ "  winning worker id: " + this.winningWorkerId + "\n"
							+ "  winning worker time: " + this.winningTimeElapsedInSeconds + " seconds");
					return formula;
				}
			}
		}
		finally {
			lock.unlock();
			this.cleanUpWorkers();
		}

		// if we reach this point it means that we could not synthesize a formula
		return Formula.UNSAT();
	}
	
	private void cleanUpWorkers() {
		this.threadPool.shutdownNow();
		for (FormulaSynthWorker worker : this.workers) {
			worker.kill();
		}
	}
}
