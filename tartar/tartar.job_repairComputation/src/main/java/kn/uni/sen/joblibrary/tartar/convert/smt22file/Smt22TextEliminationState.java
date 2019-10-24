package kn.uni.sen.joblibrary.tartar.convert.smt22file;

import java.util.List;

import kn.uni.sen.joblibrary.tartar.convert.smt2.model.ClockSmt2;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.ModelSmt2;
import kn.uni.sen.jobscheduler.common.model.JobContext;

public class Smt22TextEliminationState extends Smt22Text
{
	int stateIndex = 0;

	public Smt22TextEliminationState(boolean command, int state, JobContext context)
	{
		super(false, command, context);
		this.stateIndex = state;
		variant = "; output state quantifier elimination\n";
		fileExtra = "_stateqe" + stateIndex;
	}

	String getPositiveClock(List<ClockSmt2> clockList, int nodeCount)
	{
		String text = "";
		int index = 1;
		// every di delay variable is > 0
		for (ClockSmt2 clock : clockList)
		// if (clock.getOrigin().compareTo(t0Name) != 0)
		{
			if (clock.getOrigin().compareTo(t0Name) != 0)
				// continue;
				if (stateIndex == clock.getIndex())
					continue;
			if (index != clock.getIndex())
			{
				index = clock.getIndex();
				text += "\n";
			}
			text += "(" + clock.getName() + " Real)";
		}
		text += "\n";
		return text;
	}

	@Override
	public String assertText(String val)
	{
		if (val == null)
			return "";
		return val + "\n";
	}

	@Override
	public String assertSoftText(String val)
	{
		if (val == null)
			return "";
		// assert-soft would be set to 0 with qe
		// return val + "\n";
		return "";
	}

	public String getCommand()
	{
		if (!!!command)
			return "";
		String text = "(echo \"--- apply qe-light\")\n";
		text += "(apply qe-light)\n";
		text += "(get-info :all-statistics)\n\n";

		text += "(echo \"--- apply qe2\")\n";
		text += "(apply qe2)\n";
		text += "(get-info :all-statistics)\n\n";

		text += "(echo \"--- apply qe\")\n";
		text += "(apply qe)\n";
		text += "(get-info :all-statistics)\n\n";

		text += "(echo \"-- quantifier elimination finished\")\n";
		return text;
	}

	@Override
	public String transform(ModelSmt2 smt2)
	{
		this.smt2 = smt2;
		if (smt2 == null)
			return null;

		// preprocessTrace();

		String text = start;
		text += "; symbolic trace: " + smt2.getModelName() + "\n";
		text += smt2.getStartComment();
		text += variant + "\n";
		if (logic != null)
			text += "(set-logic " + logic + ")\n";

		int count = smt2.getTransitionList().size();
		List<ClockSmt2> clockList = smt2.getClockList();
		text += getDefineClockList(clockList);
		text += getDeclareVariables();

		text += "(assert\n";
		text += "(exists\n";
		text += "(\n";

		text += getPositiveClock(clockList, count);

		text += ")\n(and\n";

		text += getInitialClock(clockList);
		//text += super.getPositiveClockList(clockList);
		text += getDefineVariables();
		text += getDelayBoundary(clockList, count);
		text += getTrace(smt2);

		text += ") ; and\n";
		text += ") ; exists\n";
		text += ") ; assert\n\n";

		text += getCommand();
		return text;
	}
}
