package jfuzz.util;

import java.math.BigInteger;

public class BigIntegerEEA {

	public BigInteger iA, iB, gcd;

    public BigIntegerEEA(BigInteger A, BigInteger B) {
    	BigInteger K = A;
    	BigInteger M = B;
        BigInteger x     = BigInteger.ZERO;
        BigInteger lastx = BigInteger.ONE;
        BigInteger y     = BigInteger.ONE;
        BigInteger lasty = BigInteger.ZERO;
        while (!M.equals(BigInteger.ZERO)) {

        	BigInteger[] quotientAndRemainder = K.divideAndRemainder(M);
            BigInteger quotient = quotientAndRemainder[0];

            BigInteger temp = K;
            K = M;
            M = quotientAndRemainder[1];

            temp = x;
            x = lastx.subtract(quotient.multiply(x));
            lastx = temp;

            temp = y;
            y = lasty.subtract(quotient.multiply(y));
            lasty = temp;
        }
        this.iA = lastx;
        this.iB = lasty;
        this.gcd = K;
        assert(A.multiply(iA).add(B.multiply(iB)).compareTo(gcd) == 0);
    }
}

