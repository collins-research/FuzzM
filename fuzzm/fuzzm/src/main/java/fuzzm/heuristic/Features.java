/* 
 * Copyright (C) 2017, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.heuristic;

import java.util.ArrayList;
import java.util.List;

import fuzzm.FuzzMConfiguration;
import fuzzm.util.ID;
import jkind.lustre.Expr;
import jkind.lustre.IdExpr;

public class Features {

	List<HeuristicInterface> body;
	int epocCount;
	int next;
	
	public Features(FuzzMConfiguration cfg) {
		//ExprVect v = new ExprVect(cfg.inputNames);
		List<Expr> features;
		List<String> properties = cfg.model.getMainNode().properties;
		features = new ArrayList<>();
		for (String name: properties) {
		    features.add(new IdExpr(name));
		}

		if (features.size() <= 0) {
			System.out.println(ID.location() + "*** Error: Model Suggests no Fuzzable Features");
			throw new RuntimeException();
		}
		body = new ArrayList<HeuristicInterface>();
		for (int i=0;i<features.size();i++) {
		    body.add(new PropertyHeuristic(cfg.getSpan(),features.get(i)));			
		}
		epocCount = cfg.vectors;
		next = 0;
	}
	
	public int size() {
		return body.size();
	}
	
	public boolean hasNext() {
		return (epocCount != 0);
	}

	public HeuristicInterface selectFeature(int featureID) {
		return body.get(featureID);
	}
	
	public int nextFeatureID() throws FeatureException {
		// TODO: We really want to be able to implement
		// an arbitrary heuristic here ..
		int featureID;
		int tries = 0;
		do {
			featureID = next;
			next = (next + 1) % body.size();
			tries++;
		} while ((! body.get(featureID).ready()) && (! (tries > body.size())));
		if (tries > body.size()) {
			throw new FeatureException();
		}
		epocCount = (epocCount < 0) ? -1 : epocCount-1;
		return featureID;
	}

}