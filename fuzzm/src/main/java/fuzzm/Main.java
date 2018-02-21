/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package jfuzz;

import java.util.Arrays;


/**
 * Main is the top level interface to the JFuzz tool suite.
 * The suite currently consists only of JFuzz.
 *
 */
public class Main {
	public static final String VERSION = "0.1";
	public static void main(String[] args) {
		if (args.length > 0) {
			String entryPoint = args[0];
			String[] subArgs = Arrays.copyOfRange(args, 1, args.length);
			switch (entryPoint) {
			case "-jfuzz":
				JFuzzMain.main(subArgs);
				System.exit(0);
				break;			
			}
		}
		System.out.println("JFuzz Suite " + VERSION);
		System.out.println("Available entry points: -jfuzz");
		System.exit(1);
	}
}
