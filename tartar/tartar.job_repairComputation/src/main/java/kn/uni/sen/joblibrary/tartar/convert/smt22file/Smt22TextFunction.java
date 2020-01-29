package kn.uni.sen.joblibrary.tartar.convert.smt22file;

import java.util.List;

import kn.uni.sen.jobscheduler.common.model.RunContext;
import kn.uni.sen.joblibrary.tartar.convert.Transformer;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.ClockSmt2;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.ModelSmt2;

public class Smt22TextFunction extends Smt22Text
{
	public Smt22TextFunction(boolean command, RunContext context)
	{
		super(false, command, context);
		variant = "; output function\n";
		fileExtra = "_func";
		t0Name = "p" + Transformer.t0Name;
	}

	String getPositiveClock(List<ClockSmt2> clockList, int nodeCount)
	{
		String text = "";
		int index = 1;
		// every di delay variable is > 0
		for (ClockSmt2 clock : clockList)
		{
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
		return val + "\n";
	}

	public String getCommand()
	{
		if (!!!command)
			return "";
		String text = "(check-sat)\n";
		text += "(get-model)\n";
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

		for (ClockSmt2 clock : clockList)
			clock.setConvertName("p" + clock.getOrigin());

		// text += getDefineClockList(clockList);
		// text += getDeclareVariables();

		text += "(define-fun Pi(\n";
		text += getPositiveClock(clockList, count);
		text += ")\n Bool(and\n";

		text += getInitialClock(clockList);
		//text += getPositiveClockList(clockList);
		text += getDefineVariables();
		text += getDelayBoundary(clockList, count);
		text += getTrace(smt2);

		text += ") ; and\n";
		text += ") ; define-fun\n\n";

		text += getCommand();
		return text;
	}
}
