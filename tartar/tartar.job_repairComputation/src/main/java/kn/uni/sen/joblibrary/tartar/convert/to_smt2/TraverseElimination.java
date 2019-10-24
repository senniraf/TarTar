package kn.uni.sen.joblibrary.tartar.convert.to_smt2;

import java.util.List;

import kn.uni.sen.joblibrary.tartar.convert.smt2.model.ClockSmt2;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.ConstraintSmt2;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.FunctionSmt2;

/**
 * Traverses smt2 model and creates quantifier elimination
 * 
 * @author Martin Koelbl
 */
public class TraverseElimination extends TraverseSMT2
{
	FunctionSmt2 func = null;

	public TraverseElimination(CreateSMT2 creator)
	{
		super(creator);
		variant = "; output quantifier elimination\n";
	}

	@Override
	protected void addConstraint(ConstraintSmt2 con)
	{
		if (func != null)
		{
			func.addBody(con);
			return;
		}
		creator.addFormula(con);
	}

	@Override
	protected void createModel()
	{
		if (logic != null)
			creator.addOption("set-logic", logic);

		int count = smt2.getTransitionList().size();
		List<ClockSmt2> clockList = smt2.getClockList();
		getDefineClockList(clockList);
		getDeclareVariables();

		func = new FunctionSmt2("exists", "and");
		for (ClockSmt2 clock : clockList)
			func.addParameter(clock);

		getInitialClock(clockList);
		super.getPositiveClockList(clockList);
		getDefineVariables();
		getDelayBoundary(clockList, count);
		getTrace(smt2);

		creator.addFunction(func);
		func = null;

		getCommand();
	}
}
