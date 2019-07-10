package kn.uni.sen.tartar.uppaal2smt2.smt2modify;

import kn.uni.sen.tartar.uppaal2smt2.smt2.model.ClockSmt2;
import kn.uni.sen.tartar.uppaal2smt2.smt2.model.ConstraintSmt2;
import kn.uni.sen.tartar.uppaal2smt2.smt2.model.ModelSmt2;
import kn.uni.sen.tartar.uppaal2smt2.smt2.model.StateSmt2;
import kn.uni.sen.tartar.uppaal2smt2.smt2.model.TransitionSmt2;
import kn.uni.sen.tartar.uppaal2smt2.smt2.model.VariableSmt2;

/**
 * Clones a
 * 
 * @author Martin Koelbl
 */
public class Smt2Traverse
{
	int reduceLength = 0;

	protected ModelSmt2 traverse(ModelSmt2 origin)
	{
		traverseName(origin.getModelName());

		for (VariableSmt2 var : origin.getVariableList())
			traverseVariable(var);

		// clocks are also in the variable list
		for (ClockSmt2 clock : origin.getClockList())
			traverseClock(clock);

		traverseInitial(origin.getInitialState());
		int len = origin.getTransitionList().size();
		if (reduceLength > 0)
			len -= reduceLength;
		for (int i = 0; i < len; i++)
		{
			TransitionSmt2 tran = origin.getTransitionList().get(i);
			traverseTransition(tran);
		}

		for (ConstraintSmt2 prop : origin.getPropertyList())
			traverseProperty(prop);
		return origin;
	}

	protected void traverseName(String modelName2)
	{
	}

	protected void traverseVariable(VariableSmt2 allVariableList)
	{
	}

	protected void traverseClock(ClockSmt2 clockList2)
	{
	}

	protected void traverseInitial(StateSmt2 initialState2)
	{
	}

	protected void traverseTransition(TransitionSmt2 transitionList2)
	{
	}

	protected void traverseProperty(ConstraintSmt2 prop)
	{
	}
}
