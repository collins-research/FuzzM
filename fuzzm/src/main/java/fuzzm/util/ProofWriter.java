package jfuzz.util;

import java.io.PrintWriter;

public class ProofWriter {
	
	private static PrintWriter zed;

	static {
		try {
			zed = new PrintWriter("proof.lisp","UTF-8");
			assert(zed != null);
		} catch (Throwable t) {
			System.exit(1);
		}
	}
	
	private static int thmCount = 0;
	public synchronized static void printThms(String thms, String prop, String pre, String post) {
		String p1 = "(defthmd inv1-" + thms + "_" + String.valueOf(thmCount) + " (evCex `(and " + prop + " " + pre  + post + ")))";
		String hyp = "(evAlt `" + post + " any)";
		String con = "(evAlt `(and " + prop + " " + pre + ") any)";
		String p2 = "(defthmd inv2-" + thms + "_" + String.valueOf(thmCount) + " (implies " + hyp + " " + con + "))";
		zed.println(p1);
		zed.println(p2);
		zed.flush();
		thmCount++;
	}
	public synchronized static void printThms1(String thms, String s1, String s2) {
		String p10 = "(defthmd inv1-" + thms + "_1_" + String.valueOf(thmCount) + " (evCex `(" + s1 + ")))";
		String p11 = "(defthmd inv1-" + thms + "_2_" + String.valueOf(thmCount) + " (evCex `(" + s2 + ")))";
		String hyp = "(evAlt `" + s2 + " any)";
		String con = "(evAlt `(" + s1 + ") any)";
		String p2 = "(defthmd inv2-" + thms + "_" + String.valueOf(thmCount) + " (implies " + hyp + " " + con + "))";
		zed.println(p10);
		zed.println(p11);
		zed.println(p2);
		zed.flush();
		thmCount++;
	}

}
