/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.engines.messages;

import fuzzm.engines.EngineName;

/**
 * Messages with references to features
 */
abstract public class FeatureMessage extends Message {
	public FeatureID id;
	public FeatureMessage(EngineName source, QueueName queue, FeatureID id, long sequence) {
		super(source,queue,sequence);
		this.id = id;
	}
	public FeatureMessage(EngineName source, QueueName queue, FeatureID id) {
		super(source,queue);
		this.id = id;
	}
}
