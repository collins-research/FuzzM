/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.util;


/**
 * ID implements a hierarchical naming scheme for Lustre.
 *
 */
public class ID {

	// Our objective is to encode hierarchy in signal names.
	// We want to use the '_' character as a delimiter.
	// It is easiest, however, to us a pair of characters.
	// We will use 'x' as our second delimiter.
	//
	// quoted <-> raw
	//     xx <-> x
	//     x_ <-> _
	//     _  <-> .
	// 
	// .binding.1.2.3
	//
	// A generated name will always start with a "." in the local context.
	//
	// An example dotted (translated) string might be:
	//
	// .nodeA_12.nodeB_2.x.3.4
	//
	// The would correspond to the encoded string:
	//
	// _nodeAx_12_nodeBx_2_x_3_4
	//
	// Which means (reading from right to left): the 4th expression in the 
	// 3rd expression constituting signal 'x' in the 2nd node call (nodeB) 
	// in the 12th node call (nodeA) of the current node.
	//
	// We have a partial ordering .. we can define a visitor that will
	// provide us with a bottom-up node ordering.
	//
	static String dottedString(String arg) {
		int size = arg.length();
		String res = "";
		for (int i=0;i<size;i++) {
			char c = arg.charAt(i);
			if (c == 'x') {
				i++;
				if (! (i < size)) break;
				c = arg.charAt(i);
			} else if (c == '_') {
				c = '.';
			}
			res += c;
		}
		return res;
	}

	static String liftID(String node, int uid, String child) {
		return node + uid + child;
	}

	static String newID(String lhs, int uid) {
		return "_" + lhs + "_" + uid;
	}
	
	public static String encodeString(String arg) {
		if (arg == null) return arg;
		int size = arg.length();
		String res = "";
		for (int i=0;i<size;i++) {
			char c = arg.charAt(i);
			if (c == 'x') {
				res += "xx";
			} else if (c == '_') {
				res += "x_";
			} else {
				res += c;
			}
		}
		return res;
	}
	
	public static String decodeString(String arg) {
		if (arg == null) return arg;
		int size = arg.length();
		String res = "";
		for (int i=0;i<size;i++) {
			char c = arg.charAt(i);
			if (c == 'x') {
				if (i+1>=arg.length()) {
					res += c;
				} else {
					char c2 = arg.charAt(i+1);
					if ((c2 == 'x') || (c2 == '_')){
						res += c2;
						i++;
					} else {
						res += c;
					}
				}
			}
			else{
				res += c;
			}
		}
		return res;
	}
	
	public static String location() {
		return location(1);
	}

	public static String location(int depth) {
		assert(depth >= 0);
		StackTraceElement e = Thread.currentThread().getStackTrace()[2 + depth];
		String res = e.getClassName() + ":" + e.getLineNumber();
		res = res.substring(Math.max(0,res.length() - 37));
		res = String.format("%-38s",res);
		res += "| ";
		return res;
	}
	

}
