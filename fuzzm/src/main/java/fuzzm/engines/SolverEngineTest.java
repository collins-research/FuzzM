package jfuzz.engines;

import java.math.BigInteger;

import org.junit.Test;

import jfuzz.util.IntervalVector;
import jfuzz.util.JFuzzInterval;
import jfuzz.util.RatSignal;
import jfuzz.util.TypedName;
import jkind.lustre.NamedType;
import jkind.util.BigFraction;

public class SolverEngineTest {

	@Test
	public void testAsteroidTarget() {
		TypedName xIn = new TypedName("x",NamedType.INT);
		TypedName yIn = new TypedName("y",NamedType.INT);
		JFuzzInterval jfi = new JFuzzInterval(NamedType.INT, 0, 10);
		IntervalVector span = new IntervalVector();
		span.put(xIn, jfi);
		span.put(yIn, jfi);
		
		BigFraction val = new BigFraction(BigInteger.valueOf(1));
		RatSignal orig = new RatSignal();
		orig.put(0, xIn, val/*.subtract(new BigFraction(BigInteger.valueOf(5)))*/);
		orig.put(0, yIn, val.add(new BigFraction(BigInteger.valueOf(8))));
		
		BigFraction tval = new BigFraction(BigInteger.valueOf(5));
		RatSignal target = new RatSignal();
		target.put(0, xIn, tval);
		target.put(0, yIn, tval);
		
		RatSignal closest = SolverEngine.asteroidTarget(target, orig, span);
		System.out.println("closest: " + closest + "\n");
	}

}
