/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.List;

import fuzzm.heuristic.Features;
import fuzzm.lustre.AddSignals;
import fuzzm.lustre.NormalizeIDs;
import fuzzm.solver.Solver;
import fuzzm.solver.SolverName;
import fuzzm.util.IntervalVector;
import fuzzm.util.FuzzMInterval;
import fuzzm.util.FuzzMName;
import fuzzm.util.TypedName;
import jkind.ExitCodes;
import jkind.Main;
import jkind.lustre.NamedType;
import jkind.lustre.Program;
import jkind.lustre.VarDecl;
import jkind.translation.Translate;

/**
 * The essential FuzzM configuration derived from the FuzzM settings.
 *
 */
public class FuzzMConfiguration {
	
	public Path     fuzzingDirectory;
	public String   modelName;
	public Program  model;
	public List<VarDecl> inputNames;
	//public Path     inputSpecFile;
	public Path     fuzzFile;
	public int      vectors;
	public String   target;
	public List<SolverName>  userSolvers;
	private IntervalVector span;
	public boolean noVectors;
	//public boolean properties;
	//public boolean asteroid;
	public boolean throttle;
	public String configDescription;
	//public boolean unbiased;
	
	public FuzzMConfiguration(FuzzMSettings settings) {
		model = processModel(settings.filename);
		Path modelFile = Paths.get(settings.filename);
		modelName = baseModelName(modelFile);
		fuzzingDirectory = workingDirectory(modelName,settings);
		/*
		String inputSpecFileName = modelName + ".inputs";
		inputSpecFile = fuzzingDirectory.resolve(inputSpecFileName);
		try {
			Files.deleteIfExists(inputSpecFile);
			Files.createFile(inputSpecFile);} 
		catch (IOException e) {}
		*/
		inputNames = processInputs();
		fuzzFile = fuzzingDirectory.resolve("fuzz.lus");
		vectors = settings.vectors;
		employResources(fuzzingDirectory);
		target = settings.target;
		userSolvers = settings.userSolvers;
		noVectors = settings.noVectors;
		//properties = settings.properties;
		//asteroid = settings.asteroid;
		throttle = settings.throttle;
		//unbiased = settings.unbiased;
		// This singular span instance will be updated when we learn the true bounds
		// on each of the inputs. 
		span = new IntervalVector();
		for (VarDecl vd: inputNames) {
			span.put(new TypedName(vd.id,(NamedType) vd.type),new FuzzMInterval((NamedType) vd.type));
		}
		configDescription = settings.configDescription;
	} 
	
	public IntervalVector getSpan() {
		return span;
	}
	
	public void setSpan(IntervalVector span) {
		this.span = span;
	}
	
	public Features extractFeatures() {
		return new Features(this);
	}
	
	public Solver configureSolver() {
		return new Solver(userSolvers,fuzzingDirectory,"fuzz",inputNames);
	}
	
	private List<VarDecl> processInputs() {
		Path InputFileName = fuzzingDirectory.resolve("fuzz.inputs");
	    try {
	    	FileWriter fw = new FileWriter(InputFileName.toFile());
	    	for (VarDecl vdecl: model.getMainNode().inputs) {
	    		fw.write(vdecl.id + " ");
	    	}
	    	fw.write("\n");
	    	fw.close();
	    } catch (IOException e) {
	    	e.printStackTrace();
	    	System.exit(ExitCodes.UNCAUGHT_EXCEPTION);
		}
	    return model.getMainNode().inputs;
	}

    private static void copyResourceToDirectory(String resourceName, Path fuzzingDirectory) {
        InputStream infile = FuzzMConfiguration.class.getResourceAsStream("/resources/" + resourceName);
        Path outfile = fuzzingDirectory.resolve(resourceName);
        try {
            Files.copy(infile, outfile);
        } catch (IOException e) {
            e.printStackTrace();
            System.exit(1);
        }
    }

    private static void employResources(Path fuzzingDirectory) {
        //copyResourceToDirectory("Makefile", fuzzingDirectory);
        copyResourceToDirectory("xml2vector.py", fuzzingDirectory);
    }
	
	private static Program processModel(String filename) {
		Program program = null;
		try {
			program = Main.parseLustre(filename);
		} catch (Exception e) {
			e.printStackTrace();
			System.exit(1);
		}
		program = Translate.translate(program);
		//program = DropProperties.drop(program);
		program = NormalizeIDs.normalize(program);
		
        // Deprecated: these were used primarily for property synthesis.
		// There is a bug in bindLocals with (pre (if .. then 0 else 1))
		//
		// program = LocalBindings.bindLocals(program);
		// program = LiftBooleans.lift(program);
		
		// Add k-counter.  We add the top level signal _k that starts at zero
		// and simply increments in each time step.  _k can be used by other
		// signals to perform multi-cycle computation.
		program = AddSignals.add_K(program);
		
		// Note: the done signal is deprecated.
		//
		// Find/Add "done" signal.  We look for a top level signal called
		// "done" (by default).  It should be a boolean signal.  It should
		// be a "single shot" meaning that it should be true for only one
		// cycle.  If no such signal is found, we create one.  The created
		// signal assumes a single step transaction.  After finding/creating
		// the signal we bind it to _done.
		program = AddSignals.add_done(program, FuzzMName.done);
		return program;
	}
	
	private static String baseModelName(Path model) {
		String modelFileName = model.getFileName().toString();
		int dotIndex=modelFileName.lastIndexOf('.');
		String oname = modelFileName;
		if(dotIndex>=0) { // to prevent exception if there is no dot
			oname=modelFileName.substring(0,dotIndex);
		}
		return oname;
	}
	
	private static Path workingDirectory(String modelName, FuzzMSettings settings) {
		Path tempParent = Paths.get(settings.wdirName);
		Path res = null;
		try {
			String prefix = "fuzzm_" + modelName + "_";
			res = Files.createTempDirectory(tempParent,prefix);
		} catch (IOException e) {
			e.printStackTrace();
			System.exit(ExitCodes.UNCAUGHT_EXCEPTION);
		}
		res.toFile().deleteOnExit();
		return res;
	}
	
	public static boolean deleteDir(File dir) {
	    if (dir.isDirectory()) {
	        String[] children = dir.list();
	        for (int i = 0; i < children.length; i++) {
	            boolean success = deleteDir(new File(dir, children[i]));
	            if (!success) {
	                return false;
	            }
	        }
	    }
	    return dir.delete(); // The directory is empty now and can be deleted.
	}

	public void exit() {
		 try {deleteDir(fuzzingDirectory.toFile());} catch (Throwable t) {}
	}

	public void start() {		
	}
}
