package jfuzz.util;

/**
 * JFuzzName enumerates the special variable names used
 * at various points by JFuzz.
 *
 */
public class JFuzzName {
	public static final String fuzzProperty = "__fuzzProperty";
	public static final String time         = "__time";
	public static final String done         = "__done";
	public static final String boundingBox  = "__boundingBox_";
	public static final String pivotDot     = "__pivotDot_";
	public static final String region       = "__region_";
	public static final String assertion    = "__assertion_";
	public static final String exprCtxName  = "_exprCtxName_";
}
