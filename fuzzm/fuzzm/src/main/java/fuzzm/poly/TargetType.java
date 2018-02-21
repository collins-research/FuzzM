/* 
 * Copyright (C) 2018, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.poly;

public enum TargetType {
    /***
     * This value tracks whether a given variable relation should
     * be a target for inversion when generating driving hypotheses.
     * 
     * A target type can be imputed or inherited.
     * 
     * Imputed: Given the conjunction (x[F] and y[T]), if condition
     * y implies !x (under cex), then x imputes target status to y.
     * For example: y = (a[2] = 2) and x = (a[2] < 0).  It makes
     * sense to attempt to satisfy the negation of y because that 
     * "frees" x.
     * 
     * We need to decide which criteria is more relevant:
     *
     * 1) X Being True  forces Y to be False [a] = 10, X:(a = 10) Y:not(a > 5) 
     * 2) X being False allows Y to be True  [a] = 10, X:(a > 9)  Y:not(a = 10)
     *
     * cex    X (T)      Y(F)      X.target
     * a[5]  (a == 5)  !(a == 5)   Target <I think we always target True equalities>
     * a[5]  (a == 5)  !(a <= 7)   Target
     * a[5]  (a <= 7)  !(a == 5)   Chaff  <False equalities never induce Targeting>
     * a[5]  (a <= 7)  !(a <= 9)   Target  X.ub < Y.ub
     * a[5]  (a <= 7)  !(a <  6)   Chaff   Y.ub < X.ub ;; andFF should choose most extreme bound
     * a[5]  (a <= 7)  !(a >  4)   Chaff   <any opposing comparison>
     * 
     * 
     * Inherited: Given the conjunction (x[T] and y[T]), if x
     * subsumes y, x should be a target if y was a target.  For
     * example: x = (a[11] > 10) and y = (a[11] > 5).  If y is
     * a target for inversion, x should be, too.
     * 
     * Can target status ever be rescinded?
     */
    TARGET,
    CHAFF;
    public TargetType inherit(TargetType subsumed) {
        return (this == TARGET) ? this : subsumed;
    }
    public TargetType impute(boolean YimpliesXbar) {
        return YimpliesXbar ? TARGET : this;
    }
    @Override
    public String toString() {
        return (this == TARGET) ? "@" : "";
    }
}
