/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.util;

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;

import org.junit.Assert;
import org.junit.Test;

import jkind.lustre.NamedType;
import jkind.util.BigFraction;

public class RatTest {
	
	public static void main(String[] args) {

		testBias();
		//testRandom();
		//testRandomCoverage();
			
/*		int res = doublePrecision();	
		System.out.println(res);*/
			
		System.out.println("Done with RatTest main");
		
	} // end main()
	
	/*
   	   Tests-  Do we always produce min and max values for an INT range.   
	   Output-  1) and 2) activated by local boolean variables fileOutput and stdOutput, respectively:  
		   1) Writes output values and their frequency to a file (value, freq).  One value per line.  
	       2) Prints missing integer values (integers with frequency 0) to StdOut. 
	 */
	// TODO:  fixed random seed to avoid non-determinism?
	@Test
	public void testRandomCoverage() {
		try {

			System.out.println("Testing random coverage" + "\n");

			boolean stdOutput = true;
			boolean fileOutput = false;

			final int totalCount = 10000;
			final NamedType nt = NamedType.INT;
			final int minI = -128;
			final int maxI = 127;		
			final BigFraction min = new BigFraction(BigInteger.valueOf(minI));
			final BigFraction max = new BigFraction(BigInteger.valueOf(maxI));

			ArrayList<Integer> bias = new ArrayList<Integer>();
			bias.add(-1);
			bias.add(0);
			bias.add(1);

			int aBias;

			ArrayList<Integer> missing = new ArrayList<Integer>();

			for(int bIndex = 0; bIndex < bias.size(); bIndex++){

				aBias = bias.get(bIndex);

				if(stdOutput){
					System.out.println("bias: " + aBias);
				}

				BufferedWriter myOut = null;

				if(fileOutput){
					String myFileName = buildOutputFilename("random_freq_", aBias, totalCount);
					String rangeString = "_range_" + min + "--" + max;
					String typeString = "_type-" + nt.toString();
					myFileName = myFileName.concat(rangeString).concat(typeString).concat(".txt");

					myOut = new BufferedWriter(new FileWriter(myFileName));
					System.out.println(myFileName + "\n");
				}

				HashMap<Integer,Integer> hm = new HashMap<Integer, Integer>();

				for(int i = 0; i < totalCount; i += 1){

					BigFraction resBF = Rat.biasedRandom(nt, true, aBias, min, max);
					double res = resBF.doubleValue();

					if(hm.containsKey((int)res)){
						Integer freq = hm.get((int)res);
						freq = freq + 1;
						hm.put((int)res, freq);
					}
					else
					{
						hm.put((int)res, 1);
					}

				} // end for totalCount

				// output frequencies to file, one value per line.  format:  value, frequency 
				if(fileOutput){
					for(int i = minI; i <= maxI; i++){
						if(hm.containsKey(i)){
							int freq = hm.get(i);
							myOut.write(i + ", " + freq + "\n");
						}
						else
							myOut.write(i + ", " + 0 + "\n");

					}
				} // end if stdOutput

				if(! (myOut==null)){
					myOut.close();				
				}

				for(int i = minI; i <= maxI; i++){
					if(! hm.containsKey(i))
						missing.add(i);		
				}

				if(stdOutput){
					System.out.println("missing count: " + missing.size());
					System.out.println("missing: \n" + missing + "\n");
				}

				// test conditions:  Ensure we always produce min and max values.
				Assert.assertFalse(missing.contains(minI));
				Assert.assertFalse(missing.contains(maxI));

				missing.clear();

			} // end for bIndex
		} catch (Throwable e) {
			throw new Error(e);
		}
	} // end testRandomCoverage()		
		

	public static void testRandom() {
		try {
			System.out.println("Testing random()" + "\n");

			final int totalCount = 1000000;
			final NamedType nt = NamedType.REAL;
			final int minI = -128;
			final int maxI = 127;	
			final BigFraction min = new BigFraction(BigInteger.valueOf(minI));
			final BigFraction max = new BigFraction(BigInteger.valueOf(maxI));

			int lowExtremeCount, highExtremeCount;

			final int [] bias = {-1, 0, 1};
			int aBias;

			for(int bIndex = 0; bIndex < 3; bIndex++){

				aBias = bias[bIndex];

				String myFileName = buildOutputFilename("random_", aBias, totalCount);
				String rangeString = "_range_" + min + "--" + max;
				String typeString = "_type-" + nt.toString();
				myFileName = myFileName.concat(rangeString).concat(typeString).concat(".txt");
				BufferedWriter myOut = new BufferedWriter(new FileWriter(myFileName));
				System.out.println("writing to: " + myFileName + "\n");

				lowExtremeCount = highExtremeCount = 0;
				for(int i = 0; i < totalCount; i += 1){

					BigFraction resBF = Rat.biasedRandom(nt, true, aBias, min, max);
					double res = resBF.doubleValue();

					myOut.write(res + "\n");

					double range = max.doubleValue() - min.doubleValue();

					double lowCutoff = min.doubleValue()  + (1.0/3.0)*range;
					double highCutoff = min.doubleValue() + (2.0/3.0)*range;

					if(res < lowCutoff)
						lowExtremeCount++;

					if(res > highCutoff)
						highExtremeCount++;

				} // end for count

				myOut.close();

				System.out.println("bias: " + aBias);
				System.out.println("low: " + lowExtremeCount);
				System.out.println("high: " + highExtremeCount);
				System.out.println("extreme:" + (lowExtremeCount + highExtremeCount));

				double hto = (double) ((double)highExtremeCount / (((double)totalCount)-(double)highExtremeCount));
				double lto = (double) ((double)lowExtremeCount / (((double)totalCount)-(double)lowExtremeCount));
				System.out.println("high-to-other:" + hto);
				System.out.println("low-to-other:" + lto);			
				System.out.println();

			} // end for bIndex
		} catch (Throwable e) {
			throw new Error(e);
		}
	} // end testRandom()
	
	
	public static void testBias() {
		try {
			System.out.println("Testing bias()" + "\n");

			final double inc = 0.001;
			final int totalCount = (int)(1.0 / inc);

			final int [] bias = {-1, 0, 1};
			int aBias;

			int lowExtremeCount, highExtremeCount;


			for(int bIndex = 0; bIndex < 3; bIndex++){

				aBias = bias[bIndex];

				String myFileName = buildOutputFilename("bias_", aBias, totalCount);
				myFileName.concat(".txt");
				BufferedWriter myOut = new BufferedWriter(new FileWriter(myFileName));
				System.out.println("wrote to: " + myFileName + "\n");

				lowExtremeCount = highExtremeCount = 0;
				for(double i = 0; i < 1; i += inc){
					double res = Rat.pubBias(i, aBias);
					myOut.write(res + "\n");

					double highCutoff = (2.0/3.0);
					double lowCutoff = (1.0/3.0);

					if(res < lowCutoff)
						lowExtremeCount++;

					if(res > highCutoff)
						highExtremeCount++;

				} // end for inc

				myOut.close();

				System.out.println("bias: " + aBias);
				System.out.println("low: " + lowExtremeCount);
				System.out.println("high: " + highExtremeCount);
				System.out.println("extreme:" + (highExtremeCount + lowExtremeCount));

				double hto = (double) ((double)highExtremeCount / (((double)totalCount)-(double)highExtremeCount));
				double lto = (double) ((double)lowExtremeCount / (((double)totalCount)-(double)lowExtremeCount));
				System.out.println("high-to-other:" + hto);
				System.out.println("low-to-other:" + lto);
				System.out.println();

			}
		} catch (Throwable e) {
			throw new Error(e);
		}
		// end for bIndex
	} // end testBias()
	
	private static String buildOutputFilename (String prefix, int bias, int step){
		String biasString = "";
		if(bias==-1) biasString = "minus1";
		else if (bias==0) biasString = "zero";
		else if (bias==1) biasString = "plus1";

		String res = "/media/sf_mintBoxShared/" + prefix + biasString + "_step_" + step; // + ".txt";
		return res;
		
	}
	
	// This method observes the LENGTH of a range of values.  
	// Values within this range represent random double inputs that would cause our random() to output 
	//    the unlikeliest of integers (formulas assume a bias of 0, but a skewed bias would undoubtedly 
	//    make things worse).
	// If the observed range is 0.0, it means that Java's level of precision for double values makes it 
	//    IMPOSSIBLE to generate random double values that will trigger every integer output.
	// Returns the largest x such that it is possible to output all integers in the range of
	//    [0, ((2^x) - 1)].  Invocation shows that the largest range of integers fully supported is 
	//    between 2^14 and 2^15 (i.e., it is impossible to output all 16 bit integer values, 
	//    regardless of the number of input samples).  Maybe this is ok, since we don't care about outputs
	//    towards the middle of the distribution.
	// TODO:  Make formula correspond to the implementation (this method uses a hard-coded formula 
	//        derived by hand based on the current setup).
	public static int doublePrecision (){
		
		double min = -1; //-129.0;
		int power = 9;
		
		double z = -1;
		while(z != 0.0){
					
			power++;

			double max = Math.pow(2,power) + 1.0;//128.0;
			double range = max - min;
			
			double x = (Math.pow((1.0 / range), 4.0) / 2.0) + 0.5;
			double y = (Math.pow((3.0 / range), 4.0) / 2.0) + 0.5;
						
	/*		double max = 257.0;
			double x = Math.pow( (((129.0/257.0) -0.5) / (0.5)), 4.0) * 0.5 + 0.5;
			System.out.println(x);
			double y = Math.pow(((130.0/257.0) -0.5) /(0.5), 4.0) * 0.5 + 0.5;
			System.out.println(y);*/
				
			z = y - x;
		} // end while
		
		return (power-1);
		
	} // end doublePrecision
	
	

} // end class RatTest
