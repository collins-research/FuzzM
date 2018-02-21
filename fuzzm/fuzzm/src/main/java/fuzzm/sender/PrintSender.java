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
import fuzzm.util.ID;
import fuzzm.util.RatSignal;
import fuzzm.util.RatVect;
import fuzzm.util.TypedName;

/***
 * 
 * The printSender class simply prints transmitted
 * values to stdout.
 *
 */
public class PrintSender extends Sender {

	long count;
	
	public PrintSender() {
		this.count = 0;
	}

	@Override
	public void send(TestVectorMessage tv) {
        if (count % 10 == 0) {
            ProcessRatSignal(tv.signal, "TestVect");
        }
	}

    @Override
    public void send(CounterExampleMessage cex) {
        ProcessRatSignal(cex.counterExample, "CEX");
    }

    void ProcessRatSignal (RatSignal values, String label) {
        count++;
        int time = 0;
        for (RatVect r: values) {
            String value = "";
            boolean delimit = false;
            // Does this do it in an appropriate order?
            for (TypedName key: r.keySet()) {
                if (delimit) value = value.concat(" ");
                value = value.concat(r.get(key).toString());
                delimit = true;
            }
            System.out.println(ID.location() + label + " Vector[" + time + "] : " + value);
            time++;
        }
    }

}
