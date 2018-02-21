package jfuzz.sender;

import jfuzz.engines.messages.CounterExampleMessage;
import jfuzz.engines.messages.TestVectorMessage;
import jfuzz.util.ID;
import jfuzz.util.RatSignal;
import jfuzz.util.RatVect;
import jfuzz.util.TypedName;

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
