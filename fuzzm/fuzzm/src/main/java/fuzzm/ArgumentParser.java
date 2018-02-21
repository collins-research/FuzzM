/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm;

import java.math.BigInteger;

import org.apache.commons.cli.BasicParser;
import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.HelpFormatter;

/**
 * A refactoring of the JKind ArgumentParser class.
 *
 */
public abstract class ArgumentParser  {
	
	public String filename = null;
	protected static final String VERSION = "version";
	protected static final String HELP = "help";
	protected String name;
	
	public ArgumentParser(String name) {
		this.name = name;
	}
	
	public void parseArguments(String[] args) {
		CommandLineParser parser = new BasicParser();
		try {
			parseCommandLine(parser.parse(getOptions(), args));
		} catch (Throwable t) {
			throw new IllegalArgumentException(t);
		}
	}

	protected DefaultOptions getOptions() {
		DefaultOptions options = new DefaultOptions();
		options.addOption(VERSION, false, "display version information");
		options.addOption(HELP, false, "print this message");
		return options;
	}

	protected void parseCommandLine(CommandLine line) {
		if (line.hasOption(VERSION)) {
			System.out.println(name + " " + Main.VERSION);
			System.exit(0);
		}
		if (line.hasOption(HELP)) {
			printHelp();
			System.exit(0);
		}
		String[] input = line.getArgs();
		if (input.length != 1) {
			throw new IllegalArgumentException("Invalid Arguments");
		}
		filename = input[0];
	}

	public final void parse(String[] args) {
		try {
			parseArguments(args);
			checkSettings();
		} catch (IllegalArgumentException t) {
			System.err.println("");
			System.err.println(t.getMessage());
			System.err.println("");
			printHelp();
			System.exit(1);
		}
	}
	
	protected void checkSettings() {
		if (filename == null) {
			throw new IllegalArgumentException("Uninitialized Settings");
		}
	}
	
	protected void printHelp() {
		HelpFormatter formatter = new HelpFormatter();
		formatter.printHelp(name.toLowerCase() + " [options] <input>", getOptions());
	}

	protected static int parseNonnegativeInt(String text) {
		BigInteger bi = new BigInteger(text);
		if (bi.compareTo(BigInteger.ZERO) < 0) {
			return 0;
		} else if (bi.compareTo(BigInteger.valueOf(Integer.MAX_VALUE)) > 0) {
			return Integer.MAX_VALUE;
		} else {
			return bi.intValue();
		}
	}
	
	protected static void ensureExclusive(CommandLine line, String opt1, String opt2) {
		if (line.hasOption(opt1) && line.hasOption(opt2)) {
			throw new IllegalArgumentException("cannot use option -" + opt1 + " with option -"
					+ opt2);
		}
	}
}
