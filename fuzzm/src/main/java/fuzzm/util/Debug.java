package jfuzz.util;

public class Debug {

	private static boolean enabled = false;
	private static boolean logic   = false;

	public static boolean isEnabled() {
		return enabled;
	}

	public static boolean logic() {
		return logic;
	}

	public static void setEnabled(boolean enabled) {
		if ((! Debug.enabled) && enabled) System.out.println(ID.location(1) + "Enabling Debug ..");
		if (Debug.enabled && (! enabled)) System.out.println(ID.location(1) + "Disabling Debug.");
		Debug.enabled = enabled;
	}

	public static void setLogic(boolean enabled) {
		if ((! Debug.logic) && enabled) System.out.println(ID.location(1) + "Enabling Logic ..");
		if (Debug.logic && (! enabled)) System.out.println(ID.location(1) + "Disabling Logic.");
		Debug.logic = enabled;
	}
}
