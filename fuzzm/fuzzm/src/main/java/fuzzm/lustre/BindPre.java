/* 
 * Copyright (C) 2018, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.lustre;

import java.util.ArrayList;
import java.util.List;

import jkind.lustre.BoolExpr;
import jkind.lustre.Equation;
import jkind.lustre.Expr;
import jkind.lustre.IdExpr;
import jkind.lustre.IntExpr;
import jkind.lustre.Node;
import jkind.lustre.Program;
import jkind.lustre.RealExpr;
import jkind.lustre.UnaryExpr;
import jkind.lustre.UnaryOp;
import jkind.lustre.VarDecl;
import jkind.lustre.builders.NodeBuilder;
import jkind.lustre.visitors.TypeAwareAstMapVisitor;
import jkind.translation.FlattenPres;

/**
 * Bind expressions appearing in 'pre'.
 */
public class BindPre extends TypeAwareAstMapVisitor {
    public static Program program(Program program) {
        return new FlattenPres().visit(program);
    }

    private List<VarDecl> newLocals = new ArrayList<>();
    private List<Equation> newEquations = new ArrayList<>();
    private int counter = 0;

    @Override
    public Node visit(Node e) {
        NodeBuilder builder = new NodeBuilder(super.visit(e));
        builder.addLocals(newLocals);
        builder.addEquations(newEquations);
        return builder.build();
    }

    private IdExpr getFreshId() {
        return new IdExpr("~bindPre" + counter++);
    }

    @Override
    public Expr visit(UnaryExpr e) {
        Expr x = e.expr.accept(this);
        if (e.op == UnaryOp.PRE && !(x instanceof IdExpr || x instanceof IntExpr || x instanceof BoolExpr || x instanceof RealExpr)) {
            IdExpr id = getFreshId();
            newLocals.add(new VarDecl(id.id, getType(e.expr)));
            newEquations.add(new Equation(id,x));
            return new UnaryExpr(e.op, id);
        } else {
            return new UnaryExpr(e.op,x);
        }
    }
}

