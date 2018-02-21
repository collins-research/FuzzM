package jfuzz.sender;

import jfuzz.engines.messages.CounterExampleMessage;
import jfuzz.engines.messages.TestVectorMessage;

/***
 * 
 * The Sender class transmits fuzzing values to a target.
 * 
 */
public abstract class Sender {
	abstract public void send(TestVectorMessage tv);
	abstract public void send(CounterExampleMessage cex);
}
