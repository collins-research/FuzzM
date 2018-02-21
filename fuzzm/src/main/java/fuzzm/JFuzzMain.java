package jfuzz;

import jfuzz.engines.Director;

/**
 * JFuzzMain is the interface to the JFuzz functionality.
 *
 */
public class JFuzzMain {

	public static void main(String[] args) {
		try {
			JFuzzSettings settings = new JFuzzSettings();
			settings.parse(args);
			JFuzzConfiguration cfg = new JFuzzConfiguration(settings);
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
