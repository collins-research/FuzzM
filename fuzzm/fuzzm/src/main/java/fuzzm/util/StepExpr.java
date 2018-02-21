/* 
 * Copyright (C) 2018, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.util;

import jkind.lustre.Expr;

public class StepExpr {
   public int  step;
   public Expr expr;
   public StepExpr(int step, Expr expr) {
       this.step = step;
       this.expr = expr;
   }
}
