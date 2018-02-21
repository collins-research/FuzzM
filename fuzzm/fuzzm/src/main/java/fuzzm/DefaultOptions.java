/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm;

import org.apache.commons.cli.Options;

/**
 * DefaultOptions extends Options providing an addOption()
 * method that accepts an additional default value argument.
 *
 */
public class DefaultOptions extends Options {
	private static final long serialVersionUID = 1L;
	public DefaultOptions addOption(String opt, boolean hasArg, String description, Object defaultValue) {
		String defaultValueString = (defaultValue == null) ? "null" : defaultValue.toString();
		String altDescription = description + " [" + defaultValueString + "]";
		addOption(opt,hasArg,altDescription);
		return this;
	}
}
