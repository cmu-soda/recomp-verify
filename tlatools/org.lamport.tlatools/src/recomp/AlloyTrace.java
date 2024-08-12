package recomp;

public class AlloyTrace {
	private final boolean hasError;
	private final String name;
	private final String ext;
	private final int lastIdx;
	private final String alloyLastIdx;
	private final String path;
	private final int size;
	
	public AlloyTrace() {
		this.hasError = false;
		this.name = null;
		this.ext = null;
		this.lastIdx = -1;
		this.alloyLastIdx = null;
		this.path = null;
		this.size = 0;
	}
	
	public AlloyTrace(final String name, final String ext, final int lastIdx, final String alloyLastIdx,
			final String path, final int size) {
		this.hasError = true;
		this.name = name;
		this.ext = ext;
		this.lastIdx = lastIdx;
		this.alloyLastIdx = alloyLastIdx;
		this.path = path;
		this.size = size;
	}
	
	public boolean hasError() {
		return this.hasError;
	}
	
	public String name() {
		return this.name;
	}
	
	public int lastIdx() {
		return this.lastIdx;
	}
	
	public String alloyLastIdx() {
		return this.alloyLastIdx;
	}
	
	public String path() {
		return this.path;
	}
	
	public int size() {
		return this.size;
	}
	
	public boolean isEmpty() {
		return this.size == 0;
	}
	
	public String fullSigString() {
		return "one sig " + this.name + " extends " + this.ext + " {} {\n"
			+ "	lastIdx = " + this.alloyLastIdx + "\n"
			+ "	path = " + this.path + "\n"
			+ "}";
	}
	
	@Override
	public String toString() {
		return "one sig " + this.name + " extends " + this.ext + " {} {}";
	}
}
