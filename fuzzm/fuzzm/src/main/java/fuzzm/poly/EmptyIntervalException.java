/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.poly;

public class EmptyIntervalException extends IllegalArgumentException {

	public EmptyIntervalException(String string) {
		super(string);
	}

	public EmptyIntervalException() {
		super();
	}

	private static final long serialVersionUID = -4966015555719606305L;

}
