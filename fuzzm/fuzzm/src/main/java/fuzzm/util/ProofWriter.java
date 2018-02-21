/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.util;

import java.io.PrintWriter;

public class ProofWriter {
	
	private static PrintWriter zed = null;

	private static void init() {
		try {
			zed = new PrintWriter("proof.lisp","UTF-8");
			assert(zed != null);
            zed.println("(include-book \"misc/eval\" :dir :system)");
		} catch (Throwable t) {
			System.exit(1);
		}
	}
	
	private static int thmCount = 0;
	public synchronized static void printAndTT(String loc, String thms, String prop, String pre, String post) {
	    if (! Debug.proof()) return;
	    if (zed == null) init();
		String p1 = "(defthm inv1-" + thms + "_" + String.valueOf(thmCount) + " (evCex `(and " + prop + " " + pre  + post + "))\n :hints ((\"Goal\" :do-not '(preprocess))) :rule-classes nil)";
		String hyp = "(evAlt `" + post + " any)";
		String con = "(evAlt `(and " + prop + " " + pre + ") any)";
		String p2 = "(defthm inv2-" + thms + "_" + String.valueOf(thmCount) + " (implies " + hyp + " " + con + ")\n :hints ((\"Goal\" :do-not '(preprocess))) :rule-classes nil)";
		zed.println(";; " + loc);
		zed.println(p1);
		zed.println(p2);
		zed.flush();
		thmCount++;
	}
    public synchronized static void printAnd2(String loc, String thm, String x, String y, String res) {
        if (! Debug.proof()) return;
        if (zed == null) init();
        String p1 = "(defthm inv1-" + thm + "_" + String.valueOf(thmCount) + " (iff (evCex `(and " + x + "\n" + y + ")) \n (evCex `" + res + "))\n :hints ((\"Goal\" :do-not '(preprocess))) :rule-classes nil)";
        zed.println(";; " + loc);
        zed.println(p1);
        zed.flush();
        thmCount++;
    }
	public synchronized static void printRefinement(String loc, String thms, String formula, String generalization) {
	    if (! Debug.proof()) return;
	    if (zed == null) init();
	    String formulaCex = "(evCex `" + formula + ")";
        String generalizationCex = "(evCex `" + generalization + ")";
        String inv1 = "(defthm inv1-" + thms + "_" + String.valueOf(thmCount) + "\n (iff " + generalizationCex + "\n      " + formulaCex + ")\n :hints ((\"Goal\" :do-not '(preprocess))) :rule-classes nil)";
		String formulaAny = "(evAlt `" + formula + " any)";
		String generalizationAny = "(evAlt `" + generalization + " any)";
		String hyp = "(iff " + formulaAny + " (not " + formulaCex + "))";
		String con = "(iff " + generalizationAny + " " + formulaAny + ")";
        String inv2 = "(defthm inv2-" + thms + "_" + String.valueOf(thmCount) + "\n (implies\n  " + hyp + "\n  " + con + ")\n :hints ((\"Goal\" :do-not '(preprocess))) :rule-classes nil)";
		zed.println(";; " + loc);
        zed.println(inv1);
		zed.println(inv2);
		zed.flush();
		thmCount++;
	}
	public synchronized static void printThm(String loc, String name, boolean target, String H, String C) {
	    if (! Debug.proof()) return;
        if (zed == null) init();
        String He = "(evCEX `" + H + ")";
        String Ce = "(evCEX `" + C + ")";
        String body = "(implies " + He + " " + Ce + ")";        
        String defthm = "(defthm " + name + "_" + String.valueOf(thmCount) + "\n" + body + "\n :hints ((\"Goal\" :do-not '(preprocess))) :rule-classes nil)";
        String event = target ? defthm : "(must-fail\n" + defthm + ")";
        zed.println(";; " + loc);
        zed.println(event);
        zed.flush();
        thmCount++;
	}
    public synchronized static void printEval(String loc, String name, String zoid, String any) {
        if (! Debug.proof()) return;
        if (zed == null) init();
        String body = "(evAlt `" + zoid + " " + any + ")";
        String event = "(defthm " + name + "_" + String.valueOf(thmCount) + "\n" + body + "\n :hints ((\"Goal\" :do-not '(preprocess))) :rule-classes nil)";
        zed.println(";; " + loc);
        zed.println(event);
        zed.flush();
        thmCount++;
    }

}
