/* 
 * Copyright (C) 2018, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.lustre.generalize;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import fuzzm.poly.VariableID;
import fuzzm.poly.VariableRole;
import fuzzm.util.StepExpr;
import jkind.lustre.Expr;
import jkind.lustre.IdExpr;

public class ReMapExpr {
    /***
     *   This class allows us to map generalized variables back to
     *   expressions in the Lustre model.  Note that get() will 
     *   return the original input
     */
    private Map<VariableID,Collection<StepExpr>> remap;
    public ReMapExpr() {
        remap = new HashMap<>();
    }

    public ReMapExpr add(VariableID key, int step, Expr value) {
        Collection<StepExpr> values = remap.containsKey(key) ? remap.get(key) : new ArrayList<>();
        values.add(new StepExpr(step,value));
        remap.put(key, values);
        return this;
    }

    private static Expr namedExpr(VariableID key) {
        return new IdExpr(key.name.name.name);
    }

    public Collection<StepExpr> get(VariableID key) {
        Collection<StepExpr> values;
        if (remap.containsKey(key)) {
            values = new ArrayList<>(remap.get(key));
        } else {
            values = new ArrayList<>();
            Expr zed = (key.role == VariableRole.AUXILIARY) ? key.cexExpr() : namedExpr(key);            
            values.add(new StepExpr(key.name.time,zed));
        }
        return values;
    }
}
