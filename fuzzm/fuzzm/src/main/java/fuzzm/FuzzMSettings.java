/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm;

import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.List;
import java.util.stream.Collectors;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.Option;

import fuzzm.solver.SolverName;
import fuzzm.util.Debug;

/**
 * The user-provided settings for FuzzM.
 *
 */
public class FuzzMSettings extends ArgumentParser {
	
	public String configDescription = "";
	
	private static final String SOLUTIONS = "solutions";
	static final int solutions_default = -1;
	public int solutions = solutions_default;  // Default: Run forever

	private static final String WDIR    = "wdir";
	static final String wdirName_default = wdirDefault();
	public String wdirName = wdirName_default;   // Working directory

	//private static final String DONE    = "done";
	//public static final String doneName_default = "done";
	//public String doneName = doneName_default;
	
	private static final String TARGET = "amqp";
	public static final String target_default = null;
	String target = target_default;

	private static final String SOLVER = "solver";
	public static final SolverName solver_default = null;
	List<SolverName> userSolvers = new ArrayList<SolverName>();
	
	private static final String NOVECTORS = "no_vectors";
	public static final boolean noVectors_default = false;
	boolean noVectors = noVectors_default;
	
    private static final String PROOF = "proof";
    public static final boolean Proof_default = false;
    boolean Proof = Proof_default;
    
	private static final String CONSTRAINTS = "constraints";
	public static final boolean constraints_default = false;
	boolean constraints = constraints_default;
	
    //private static final String PROPERTIES = "properties";
    //public static final boolean properties_default = true;
    //boolean properties = properties_default;
    
	//private static final String ASTEROID = "asteroid";
	//public static final boolean asteroid_default = false;
    //boolean asteroid = asteroid_default;

	//private static final String UNBIASED = "unbiased";
	//public static final boolean unbiased_default = false;
	//boolean unbiased = unbiased_default;
	
	private static final String THROTTLE = "throttle";
	public static final boolean throttle_default = false;
	boolean throttle = throttle_default;

	private static String wdirDefault() {
		return Paths.get(".").toAbsolutePath().normalize().toString();
	}
	
	public FuzzMSettings() {
		this("FuzzM");
	}

	protected FuzzMSettings(String name) {
		super(name);
	}
	
	@Override
	protected DefaultOptions getOptions() {
		DefaultOptions options = super.getOptions();
		options.addOption(SOLUTIONS, true, "Total number of constraint solutions to attempt (-1 = forever)",solutions_default);
		options.addOption(WDIR, true, "Path to temporary working directory",wdirName_default);
		//options.addOption(DONE, true, "Top level \"done\" signal name",doneName_default);
		options.addOption(TARGET, true, "URL of AMQP server",target_default);
		options.addOption(SOLVER, true, "Use Only Specified Solver",solver_default);
		options.addOption(NOVECTORS, false, "Suppress test vector generation (debug)",noVectors_default);
		options.addOption(PROOF, false, "Generate a validating proof script (debug)",Proof_default);
        options.addOption(CONSTRAINTS, false, "Treat Lustre properties as constraints",constraints_default);
		//options.addOption(PROPERTIES, false, "Fuzz only model properties",properties_default);
        //options.addOption(ASTEROID, false, "Use asteroid space metric",asteroid_default);
		options.addOption(THROTTLE, false, "Throttle vector generation (debug)",throttle_default);
		//options.addOption(UNBIASED, false, "Disable bias when choosing values on an interval",unbiased_default);
		return options;
	}

	@Override
	protected void parseCommandLine(CommandLine line) {

		super.parseCommandLine(line);
		
		if (line.hasOption(SOLUTIONS)) {
			solutions = parseNonnegativeInt(line.getOptionValue(SOLUTIONS));
		}

		if (line.hasOption(WDIR)) {
			wdirName = line.getOptionValue(WDIR);
		}
		
		//if (line.hasOption(DONE)) {
		//	doneName = ID.encodeString(line.getOptionValue(DONE));
		//}
		
		if (line.hasOption(TARGET)) {
			target = line.getOptionValue(TARGET);
		}
		
		if (line.hasOption(NOVECTORS)) {
			noVectors = true;
		}
		
		if (line.hasOption(PROOF)) {
            Proof = true;
            Debug.setProof(true);
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
		
//		if (line.hasOption(PROPERTIES)) {
//			properties = true;
//		}
		
        if (line.hasOption(CONSTRAINTS)) {
            constraints = true;
        }
    
//		if (line.hasOption(ASTEROID)) {
//			asteroid = true;
//		}
		
		if (line.hasOption(THROTTLE)) {
			throttle = true;
		}
		
//		if (line.hasOption(UNBIASED)) {
//			unbiased = true;
//		}

		List<String> toIgnore = Arrays.asList(WDIR,VERSION,HELP);
		
		// TODO: I don't understand the need for this unchecked conversion .. Java? anyone?
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
