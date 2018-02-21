package jfuzz.poly;

abstract public class VariableInequality extends VariableRelation {

	protected VariableInequality(VariableID name, boolean cex, RelationType relation, AbstractPoly poly, FeatureType feature) {
		super(name,cex,relation,poly,feature);
	}
	
	@Override
	abstract public VariableInequality not();
	
	abstract VariableInequality chooseBestCompliment(VariableInterval arg);
	
	@Override
	public boolean requiresRestriction() {
		return false;
	}

	@Override
	public RestrictionResult restriction() {
		throw new IllegalArgumentException();
	}

	
}
