/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.poly;

import static org.junit.Assert.assertEquals;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.HashMap;
import java.util.Map;

import org.junit.Test;

import jkind.lustre.NamedType;
import jkind.util.BigFraction;

public class PolyBaseTest {

	@Test
	public void testAdd() {
		//VariableID constant = new VariableID("",0);	
		VariableID y = VariableID.principleAlloc("Y", NamedType.REAL,BigFraction.ONE);
		VariableID x = VariableID.principleAlloc("X",NamedType.REAL,BigFraction.ZERO);
		//VariableID z = VariableID.preAlloc("Z",NamedType.REAL,BigFraction.ZERO);
		
//		System.out.println(x.level);
//		System.out.println(y.level);
//		System.out.println(z.level);
		
		Map<VariableID,BigFraction> coefs = new HashMap<VariableID,BigFraction>();
		//coefs.put(constant, BigFraction.ONE);
		coefs.put(x, BigFraction.valueOf(BigDecimal.valueOf(2)));
		PolyBase poly1 = new PolyBase(coefs,BigFraction.ONE);	
		System.out.println("poly1: " + poly1);
		
		Map<VariableID,BigFraction> coefs2 = new HashMap<VariableID,BigFraction>();
		//coefs2.put(constant, BigFraction.valueOf(BigDecimal.valueOf(40)));
		coefs2.put(x, BigFraction.valueOf(BigDecimal.valueOf(5)));
		coefs2.put(y, BigFraction.valueOf(BigDecimal.valueOf(4)));
		
		PolyBase poly2 = new PolyBase(coefs2,BigFraction.valueOf(BigDecimal.valueOf(40)));
		System.out.println("poly2: " + poly2);
		
		AbstractPoly polyadd = poly1.add(poly2);
		System.out.println("poly1 + poly2: " + polyadd);
		
		AbstractPoly polyaddsub = polyadd.subtract(poly2);
		System.out.println("poly1 + poly2 - poly2: " + polyaddsub);
		
		AbstractPoly polysub = poly1.subtract(poly1);
		System.out.println("poly1 - poly1: " + polysub);
		
		AbstractPoly polyaddneg = poly1.add(poly1.negate());
		System.out.println("poly1 + (-poly1): " + polyaddneg);
		
		System.out.println("poly2 * 3: " + poly2.multiply(BigFraction.valueOf(BigDecimal.valueOf(3))));
		
		PolyBase emptyPoly = new PolyBase();
		
		Map<VariableID,BigFraction> zerocoefs = new HashMap<VariableID,BigFraction>();
		//zerocoefs.put(constant, BigFraction.ZERO);
		PolyBase constZeroPoly = new PolyBase(zerocoefs,BigFraction.ZERO);
		
		Map<VariableID,BigFraction> constFourCoef = new HashMap<VariableID,BigFraction>();
		//constFourCoef.put(constant, BigFraction.valueOf(BigDecimal.valueOf(4)));
		PolyBase constFourPoly = new PolyBase(constFourCoef,BigFraction.valueOf(BigDecimal.valueOf(4)));
		
		Map<VariableID,BigFraction> negHalfCoef = new HashMap<VariableID,BigFraction>();
		BigFraction negHalf = new BigFraction(BigInteger.valueOf(-1),BigInteger.valueOf(2));
		//negHalfCoef.put(constant, negHalf);
		PolyBase constNegHalfPoly = new PolyBase(negHalfCoef,negHalf);
		
		System.out.println("poly1 - constFour: " + poly1.subtract(constFourPoly));
		
		System.out.println("poly1 solved for x: " + poly1.solveFor(x));
		System.out.println("poly2 solved for x: " + poly2.solveFor(x));
		System.out.println("poly2 solved for y: " + poly2.solveFor(y));
		System.out.println("(poly1 - constFour) solved for x: " + poly1.subtract(constFourPoly).solveFor(x));
		
		
		System.out.println("evaluate poly1(x is ZERO by default): " + poly1.evaluateCEX());
		
		Map<VariableID,BigFraction> coefsCex1 = new HashMap<VariableID,BigFraction>();
		coefsCex1.put(y, BigFraction.valueOf(BigDecimal.valueOf(2)));
		PolyBase poly1Cex1 = new PolyBase(coefsCex1,BigFraction.ONE);
		
		System.out.println("evaluate poly1Cex1: " + poly1Cex1.evaluateCEX());
		
		x.setCex(new BigFraction(BigInteger.valueOf(2)));
		System.out.println("evaluate poly2: " + poly2.evaluateCEX());
		//System.out.println(constZeroPoly);
		//System.out.println(emptyPoly);
		
		assertEquals(poly1,polyaddsub);
		assertEquals(emptyPoly,polysub);
		assertEquals(emptyPoly,polyaddneg);
		assertEquals(emptyPoly,constZeroPoly);
		assertEquals(constNegHalfPoly, poly1.solveFor(x));
		
		
	}

}
