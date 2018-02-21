/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.sender;

import fuzzm.engines.messages.CounterExampleMessage;
import fuzzm.engines.messages.TestVectorMessage;

/***
 * 
 * The Sender class transmits fuzzing values to a target.
 * 
 */
public abstract class Sender {
	abstract public void send(TestVectorMessage tv);
	abstract public void send(CounterExampleMessage cex);
}
