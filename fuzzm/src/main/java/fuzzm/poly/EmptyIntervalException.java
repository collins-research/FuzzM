package jfuzz.poly;

public class EmptyIntervalException extends IllegalArgumentException {

	public EmptyIntervalException(String string) {
		super(string);
	}

	public EmptyIntervalException() {
		super();
	}

	private static final long serialVersionUID = -4966015555719606305L;

}
