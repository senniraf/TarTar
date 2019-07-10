package kn.uni.sen.tartar.uppaal2smt2.uppaalmodel.model;

/** general interface of a constraint in an invariant or guard
 * 
 * @author Martin Koelbl
 */

public interface ConstraintInterface
{
	public enum UppaalConstraintType
	{
		UNKOWN, VARIABLE, CONSTRAINT, CONSTANT
	}

	UppaalConstraintType getConstraintType();
}
