package recomp;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import gov.nasa.jpf.util.json.JSONObject;
import tlc2.Utils;

public class Fluent {
	public final String name;
	public final List<String> paramTypes;
	public final String initially;
	public final Set<String> init;
	public final Set<String> term;
	public final Map<String, List<Integer>> symActParamMaps;
	
	public Fluent(final String name, final JSONObject fluentInfo) {
		this.name = name;
		this.paramTypes = Utils.toArrayList(fluentInfo.getValue("paramTypes").getArray())
				.stream()
				.map(v -> v.getString())
				.collect(Collectors.toList());
		this.initially = fluentInfo.getValue("initially").getString();
		this.init = Utils.toArrayList(fluentInfo.getValue("init").getArray())
				.stream()
				.map(v -> v.getString())
				.collect(Collectors.toSet());
		this.term = Utils.toArrayList(fluentInfo.getValue("term").getArray())
				.stream()
				.map(v -> v.getString())
				.collect(Collectors.toSet());
		
		this.symActParamMaps = new HashMap<>();
		final JSONObject paramMapInfo = fluentInfo.getValue("symActParamMaps").getObject();
		for (final String act : paramMapInfo.getValuesKeys()) {
			final List<Integer> paramMap = Utils.toArrayList(paramMapInfo.getValue(act).getArray())
					.stream()
					.map(v -> v.getDouble().intValue())
					.collect(Collectors.toList());
			this.symActParamMaps.put(act, paramMap);
		}
	}
	
	public String toJson() {
		final String paramTypes = "\"paramTypes\":[" +
				this.paramTypes
					.stream()
					.map(pt -> "\"" + pt + "\"")
					.collect(Collectors.joining(","))
				+ "]";
		final String initially = "\"initially\":\"" + this.initially + "\"";
		final String init = "\"init\":[" +
				this.init
				.stream()
				.map(pt -> "\"" + pt + "\"")
				.collect(Collectors.joining(","))
			+ "]";
		final String term = "\"term\":[" +
				this.term
				.stream()
				.map(pt -> "\"" + pt + "\"")
				.collect(Collectors.joining(","))
			+ "]";
		
		final String symActMapsContents = this.symActParamMaps.keySet()
				.stream()
				.map(m -> {
					final String strMap = this.symActParamMaps.get(m)
							.stream()
							.map(i -> i.toString())
							.collect(Collectors.joining(","));
					return "\"" + m + "\":[" + strMap + "]";
				})
				.collect(Collectors.joining(","));
		final String symActMaps = "\"symActParamMaps\":{" + symActMapsContents + "}";
		
		return "{" + String.join(",", List.of(paramTypes, initially, init, term, symActMaps)) + "}";
	}
	
	@Override
	public String toString() {
		return this.name + ":\n"
				+ "  initially: " + this.initially + "\n"
				+ "  init: " + this.init.stream().collect(Collectors.joining(", ")) + "\n"
				+ "  term: " + this.term.stream().collect(Collectors.joining(", ")) + "\n"
				+ "  paramsMap: " + this.symActParamMaps.keySet()
										.stream()
										.map(p -> p + ": [" + this.symActParamMaps.get(p).stream().map(i -> ""+i).collect(Collectors.joining(",")) + "]")
										.collect(Collectors.joining("\n             "));
	}
}
