/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.engines.messages;

/**
 * Enumeration of the various queues in the system.
 */
public enum QueueName {
	CounterExampleMessage,
	ConstraintMessage,
	ExitMessage,
	GeneralizedMessage,
	TestVectorMessage,
	UnsatMessage,
	PauseMessage,
	ResumeMessage
}
