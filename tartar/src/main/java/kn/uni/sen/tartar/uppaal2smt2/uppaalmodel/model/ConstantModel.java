package kn.uni.sen.tartar.uppaal2smt2.uppaalmodel.model;

/** contains a constant of a constraint in an invariant or guard
 * 
 * @author Martin Koelbl
 */
public class ConstantModel implements ConstraintInterface
{
	String value;

	public ConstantModel(String value)
	{
		this.value = value;
	}

	public String getValue()
	{
		return value;
	}

	@Override
	public UppaalConstraintType getConstraintType()
	{
		return UppaalConstraintType.CONSTANT;
	}

}
