package recomp;

public class AlloyTrace {
	private final boolean hasError;
	private final String name;
	private final String ext;
	private final int lastIdx;
	private final String alloyLastIdx;
	private final String path;
	
	public AlloyTrace() {
		this.hasError = false;
		this.name = null;
		this.ext = null;
		this.lastIdx = -1;
		this.alloyLastIdx = null;
		this.path = null;
	}
	
	public AlloyTrace(final String name, final String ext, final int lastIdx, final String alloyLastIdx, final String path) {
		this.hasError = true;
		this.name = name;
		this.ext = ext;
		this.lastIdx = lastIdx;
		this.alloyLastIdx = alloyLastIdx;
		this.path = path;
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
	
	@Override
	public String toString() {
		return "one sig " + this.name + " extends " + this.ext + " {} {}";
		/*return "one sig " + this.name + " extends " + this.ext + " {} {\n"
				+ "	lastIdx = " + this.alloyLastIdx + "\n"
				+ "	path = " + this.path + "\n"
				+ "}";*/
	}
}
