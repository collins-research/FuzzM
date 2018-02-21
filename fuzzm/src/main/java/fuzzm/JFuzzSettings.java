package jfuzz;

import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.List;
import java.util.stream.Collectors;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.Option;

import jfuzz.solver.SolverName;
import jfuzz.util.ID;

/**
 * The user-provided settings for JFuzz.
 *
 */
public class JFuzzSettings extends ArgumentParser {
	
	public String configDescription = "";
	
	private static final String VECTORS = "vectors";
	static final int vectors_default = -1;
	public int vectors = vectors_default;  // Default: Run forever

	private static final String WDIR    = "wdir";
	static final String wdirName_default = wdirDefault();
	public String wdirName = wdirName_default;   // Working directory

	private static final String DONE    = "done";
	public static final String doneName_default = "done";
	public String doneName = doneName_default;
	
	private static final String TARGET = "target";
	public static final String target_default = null;
	String target = target_default;

	private static final String SOLVER = "solver";
	public static final SolverName solver_default = null;
	List<SolverName> userSolvers = new ArrayList<SolverName>();
	
	private static final String NOVECTORS = "no_vectors";
	public static final boolean noVectors_default = false;
	boolean noVectors = noVectors_default;
	
	private static final String PROPERTIES = "properties";
	public static final boolean properties_default = false;
	boolean properties = properties_default;
	
	private static final String ASTEROID = "asteroid";
	public static final boolean asteroid_default = false;
	boolean asteroid = asteroid_default;

	private static final String UNBIASED = "unbiased";
	public static final boolean unbiased_default = false;
	boolean unbiased = unbiased_default;
	
	private static final String THROTTLE = "throttle";
	public static final boolean throttle_default = false;
	boolean throttle = throttle_default;

	private static String wdirDefault() {
		return Paths.get(".").toAbsolutePath().normalize().toString();
	}
	
	public JFuzzSettings() {
		this("JFuzz");
	}

	protected JFuzzSettings(String name) {
		super(name);
	}
	
	@Override
	protected DefaultOptions getOptions() {
		DefaultOptions options = super.getOptions();
		options.addOption(VECTORS, true, "Number of vectors to generate (-1 = forever)",vectors_default);
		options.addOption(WDIR, true, "Path to temporary working directory",wdirName_default);
		options.addOption(DONE, true, "Top level \"done\" signal name",doneName_default);
		options.addOption(TARGET, true, "AMQP Address",target_default);
		options.addOption(SOLVER, true, "Use Only Specified Solver",solver_default);
		options.addOption(NOVECTORS, false, "Suppress test vector generation",noVectors_default);
		options.addOption(PROPERTIES, false, "Fuzz only model properties",properties_default);
		options.addOption(ASTEROID, false, "Use asteroid space metric",asteroid_default);
		options.addOption(THROTTLE, false, "Throttle vector generation",throttle_default);
		options.addOption(UNBIASED, false, "Disable bias when choosing values on an interval",unbiased_default);
		return options;
	}

	@Override
	protected void parseCommandLine(CommandLine line) {

		super.parseCommandLine(line);
		
		if (line.hasOption(VECTORS)) {
			vectors = parseNonnegativeInt(line.getOptionValue(VECTORS));
		}

		if (line.hasOption(WDIR)) {
			wdirName = line.getOptionValue(WDIR);
		}
		
		if (line.hasOption(DONE)) {
			doneName = ID.encodeString(line.getOptionValue(DONE));
		}
		
		if (line.hasOption(TARGET)) {
			target = line.getOptionValue(TARGET);
		}
		
		if (line.hasOption(NOVECTORS)) {
			noVectors = true;
		}
		
		if (line.hasOption(SOLVER)) {
			String solverName[] = line.getOptionValues(SOLVER);
			try {
				for (String name: solverName) {
					userSolvers.add(SolverName.valueOf(name.toUpperCase()));
				} 
			} catch (IllegalArgumentException e) {
				String names = SolverName.availableSolvers.stream().map(Object::toString).collect(Collectors.joining(", "));
				throw new IllegalArgumentException("Solver Must be one of: " + names);
			}
		}
		
		if (line.hasOption(PROPERTIES)) {
			properties = true;
		}
		
		if (line.hasOption(ASTEROID)) {
			asteroid = true;
		}
		
		if (line.hasOption(THROTTLE)) {
			throttle = true;
		}
		
		if (line.hasOption(UNBIASED)) {
			unbiased = true;
		}

		List<String> toIgnore = Arrays.asList(WDIR,VERSION,HELP);
		
		// TODO: I don't understand the need for this unchecked conversion ..
		@SuppressWarnings("unchecked")
		Iterator<Option> itOp = line.iterator();
		while(itOp.hasNext()){
			Option o = itOp.next();
			String name = o.getOpt();
			if(toIgnore.contains(name)){
				continue;
			}
			configDescription += name;
			if(o.getArgs() != -1){
				configDescription += ("=" + o.getValue());
			}
			configDescription += "_";
		} // end while(hasNext)
		
	} // end parseCommandLine

	@Override
	protected void checkSettings() {
		super.checkSettings();
	}
	
}
