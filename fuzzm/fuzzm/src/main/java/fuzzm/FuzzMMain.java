/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm;

import fuzzm.engines.Director;

/**
 * FuzzMMain is the interface to the FuzzM functionality.
 *
 */
public class FuzzMMain {

	public static void main(String[] args) {
		try {
			FuzzMSettings settings = new FuzzMSettings();
			settings.parse(args);
			FuzzMConfiguration cfg = new FuzzMConfiguration(settings);
			cfg.start();
			new Director(cfg).run();
			cfg.exit();
			System.exit(0);
		} catch (Throwable t) {
			t.printStackTrace();
			System.err.println("");
			System.err.println(t.getLocalizedMessage());
			System.exit(-1);
		}
	}
	
}
