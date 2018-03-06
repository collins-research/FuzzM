/* 
 * Copyright (C) 2018, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.lustre;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import fuzzm.lustre.generalize.ReMapExpr;
import fuzzm.poly.AbstractPoly;
import fuzzm.poly.PolyBase;
import fuzzm.poly.Variable;
import fuzzm.poly.VariableBoolean;
import fuzzm.poly.VariableID;
import fuzzm.poly.VariableRelation;
import fuzzm.util.FuzzmName;
import fuzzm.util.ID;
import fuzzm.util.IDString;
import fuzzm.util.StepExpr;
import jkind.lustre.BinaryExpr;
import jkind.lustre.BinaryOp;
import jkind.lustre.BoolExpr;
import jkind.lustre.CastExpr;
import jkind.lustre.Expr;
import jkind.lustre.IdExpr;
import jkind.lustre.IfThenElseExpr;
import jkind.lustre.IntExpr;
import jkind.lustre.NamedType;
import jkind.lustre.UnaryExpr;
import jkind.lustre.UnaryOp;
import jkind.util.BigFraction;

public class PolyConstraintCtx extends BooleanCtx {

    public PolyConstraintCtx(Variable v, ReMapExpr remap) {
        VariableID vid = v.vid;
        IDString name = IDString.newID(vid.name.name.name);
        Expr check = (v instanceof VariableBoolean) ? 
                     boolCheck((VariableBoolean) v,remap) :
                     polyCheck((VariableRelation) v, remap); 
        IdExpr polyConstraint = constraint(name,check);
        this.setExpr(polyConstraint);
        PolyConstraintCtx.index++;
    }
    
    private Expr boolCheck(VariableBoolean v, ReMapExpr remap) {
        VariableID vid = v.vid;
        String name = ID.cleanString(vid.name.name.name);
        StepExpr vstep = remap.get(vid).iterator().next();
        Expr id = new IdExpr(name);
        Expr polycheck = v.isNegated() ? id : new UnaryExpr(UnaryOp.NOT,id);
        Expr timecheck = new BinaryExpr(new IdExpr(FuzzmName.time.name()),BinaryOp.EQUAL,new IntExpr(BigInteger.valueOf(vstep.step)));
        Expr check = new IfThenElseExpr(timecheck,polycheck,new BoolExpr(true));
        return check;
    }
    
    private Expr polyCheck(VariableRelation v, ReMapExpr remap) {
        VariableID vid = v.vid;
        IDString name = IDString.newID(vid.name.name.name);
        NamedType type = vid.name.name.type;
        AbstractPoly poly = v.poly;
        BigInteger D = poly.leastCommonDenominator();
        poly = poly.subtract(new PolyBase(vid));
        poly = poly.multiply(new BigFraction(D));
        Map<Integer,Collection<Expr>> stepPoly = new HashMap<>();
        for (VariableID pvar : poly.getVariables()) {
            StepExpr e = remap.get(pvar).iterator().next();
            Expr vexpr = cast(pvar.name.name.type,type,e.expr);
            BigInteger C = poly.getCoefficient(pvar).getNumerator();
            Expr vcoef = cast(NamedType.INT,type,new IntExpr(C));
            Expr expr  = new BinaryExpr(vcoef,BinaryOp.MULTIPLY,vexpr);
            Collection<Expr> vals = stepPoly.containsKey(e.step) ? stepPoly.get(e.step) : new ArrayList<>();
            vals.add(expr);
            stepPoly.put(e.step,vals);
        }
        Expr ite = cast(NamedType.INT,type,new IntExpr(BigInteger.ZERO));
        int maxtime = 0;
        for (Integer time: stepPoly.keySet()) {
            maxtime = (time > maxtime) ? time : maxtime;
            BigInteger zero = (time == 0) ? poly.getConstant().getNumerator() : BigInteger.ZERO;
            Expr res = cast(NamedType.INT,type,new IntExpr(zero));
            for (Expr e: stepPoly.get(time)) {
                res = new BinaryExpr(e,BinaryOp.PLUS,res);
            }
            Expr cond = new BinaryExpr(new IdExpr(FuzzmName.time.name()),BinaryOp.EQUAL,new IntExpr(BigInteger.valueOf(time)));
            ite = new IfThenElseExpr(cond, res, ite);
        }
        IdExpr polyCoeff = this.define(name(FuzzmName.polyTerm,name), type, ite);
        IdExpr polyExpr  = poly(name,type,polyCoeff);
        Expr zero = cast(NamedType.INT,type,new IntExpr(BigInteger.ZERO));
        BinaryOp op = v.binaryOp();
        Expr polycheck = new UnaryExpr(UnaryOp.NOT,new BinaryExpr(polyExpr,op,zero));
        Expr timecheck = new BinaryExpr(new IdExpr(FuzzmName.time.name()),BinaryOp.EQUAL,new IntExpr(BigInteger.valueOf(maxtime)));
        Expr check = new IfThenElseExpr(timecheck,polycheck,new BoolExpr(true));
        return check;
    }
    
    private IdExpr poly(IDString name, NamedType type, Expr expr) {
        IdExpr z = this.declare(name(FuzzmName.polyEval,name), type);
        Expr poly = new BinaryExpr(expr,BinaryOp.ARROW,new BinaryExpr(new UnaryExpr(UnaryOp.PRE,z),BinaryOp.PLUS,expr));
        this.define(z, poly);
        return z;
    }
    
    private IdExpr constraint(IDString name, Expr expr) {
        IdExpr z = this.declare(name(FuzzmName.polyConstraint,name), NamedType.BOOL);
        Expr poly = new BinaryExpr(expr,BinaryOp.ARROW,new BinaryExpr(new UnaryExpr(UnaryOp.PRE,z),BinaryOp.AND,expr));
        this.define(z, poly);
        return z;
    }
    
    private static long index = 0;
    private static IDString name(String prefix, IDString name) {
        return name.prefix(prefix).index(index);
    }
    private static Expr cast(NamedType src, NamedType dst, Expr e) {
        if (src == dst) return e;
        return new CastExpr(dst, e);
    }
    
}
