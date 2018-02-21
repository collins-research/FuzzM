package jfuzz.poly;

public interface VariableInterface {
	
	public RestrictionResult andTrue(Variable right);
	public RestrictionResult andTrue2(VariableEquality   left);
	public RestrictionResult andTrue2(VariableInterval     left);
	public RestrictionResult andTrue2(VariableLess       left);
	public RestrictionResult andTrue2(VariableGreater    left);
	public RestrictionResult andTrue2(VariableBoolean left);
	
	public Variable andFalse(Variable right);
	public Variable andFalse2(VariableEquality   left);
	public Variable andFalse2(VariableInterval     left);
	public Variable andFalse2(VariableLess       left);
	public Variable andFalse2(VariableGreater    left);
	public Variable andFalse2(VariableBoolean    left);

}
