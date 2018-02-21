/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.solver;

import java.util.List;
import java.util.stream.Collectors;

import fuzzm.value.poly.GlobalState;
import jkind.SolverOption;
import jkind.engines.SolverUtil;

/**
 * SolverNames enumerates the names of the various solvers supported by JKind.
 *
 */
public enum SolverName {

	SMTINTERPOL("smtinterpol"), YICES2("yices2"), YICES("yices"), MATHSAT("mathsat"), CVC4("cvc4"), Z3("z3");

	private final String value;

    private SolverName(final String value) {
        this.value = value;
    }

    public String getValue() {
        return value;
    }

    public static List<SolverName> removeYICES(List<SolverName> solvers) {
    	// Because yices is deprecated by the developers and is 
    	// mis-reported by JKind when yices2 is installed we don't
    	// consider it as an option.
    	solvers.remove(YICES);
    	return solvers;
    }
    
    public static final List<SolverName> availableSolvers = removeYICES(SolverUtil.availableSolvers().stream().map(x -> asSolverName(x)).collect(Collectors.toList()));
    
    public static SolverName asSolverName(SolverOption solver) {
    	switch (solver) {
    	// SMTINTERPOL, Z3, YICES, YICES2, CVC4, MATHSAT;
    	case SMTINTERPOL: return SMTINTERPOL;
    	case Z3:          return Z3;
    	case YICES2:      return YICES2;
    	case CVC4:        return CVC4;
    	case MATHSAT:     return MATHSAT;
    	default     :     return YICES;
    	}
    }
    
    @Override
    public String toString() {
        return getValue();
    }
    
    public static SolverName randomSolver(List<SolverName> userSolvers) {
    	assert(availableSolvers.size() > 0);
    	List<SolverName> pool = (userSolvers.size() > 0) ? userSolvers : availableSolvers;
    	int choice = GlobalState.oracle().nextInt(pool.size());
    	return pool.get(choice);
    }
    
    public static SolverName randomSolver() {
    	assert(availableSolvers.size() > 0);
    	int choice = GlobalState.oracle().nextInt(availableSolvers.size());
    	return availableSolvers.get(choice);
    }
    
}
