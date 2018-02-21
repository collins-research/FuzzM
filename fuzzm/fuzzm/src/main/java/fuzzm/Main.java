/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm;

import java.util.Arrays;


/**
 * Main is the top level interface to the FuzzM tool suite.
 * The suite currently consists only of FuzzM.
 *
 */
public class Main {
	public static final String VERSION = "0.1";
	public static void main(String[] args) {
		if (args.length > 0) {
			String entryPoint = args[0];
			String[] subArgs = Arrays.copyOfRange(args, 1, args.length);
			switch (entryPoint) {
			case "-fuzzm":
				FuzzMMain.main(subArgs);
				System.exit(0);
				break;			
			}
		}
		System.out.println("FuzzM Suite " + VERSION);
		System.out.println("Available entry points: -fuzzm");
		System.exit(1);
	}
}
