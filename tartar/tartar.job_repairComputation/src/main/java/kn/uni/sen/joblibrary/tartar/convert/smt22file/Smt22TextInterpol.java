package kn.uni.sen.joblibrary.tartar.convert.smt22file;

import java.util.List;

import kn.uni.sen.joblibrary.tartar.convert.smt2.model.ClockSmt2;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.ModelSmt2;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.StateSmt2;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.TransitionSmt2;
import kn.uni.sen.jobscheduler.common.model.RunContext;

public class Smt22TextInterpol extends Smt22Text
{
	public Smt22TextInterpol(boolean command, RunContext context)
	{
		super(false, command, context);
		variant = "; output interpolation\n";
		fileExtra = "_inter";
	}

	String getPositiveClock(List<ClockSmt2> clockList, int nodeCount)
	{
		String text = "";
		int index = 1;
		// every di delay variable is > 0
		for (ClockSmt2 clock : clockList)
			if (clock.getOrigin().compareTo(t0Name) != 0)
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
		// assert-soft would be set to 0 with qe
		// return val + "\n";
		return "";
	}

	public String getCommand()
	{
		if (!!!command)
			return "";
		String text = "(check-sat)\n";
		text += "(get-interpolants ";
		text += "S1 S2 S3 S4 S5 S6 S7" + ")\n";
		text += "(exit)\n";
		return text;
	}

	protected String getTrace(ModelSmt2 smt2)
	{
		String text = "";
		StateSmt2 state = smt2.getInitialState();
		TransitionSmt2 trans = smt2.getNextTransition(state);
		int counter = 1;

		text += "(assert\n (! (and\n";
		text += getInitialClock(smt2.getClockList());
		text += ")\nnamed: S0 ))\n\n";

		text += getStateString(state, counter);
		while (trans != null)
		{
			text += "(assert\n (! (and\n";

			for (ClockSmt2 clock : smt2.getClockList())
				if (clock.getOrigin().compareTo(t0Name) == 0)
				{
					if (clock.getIndex() == counter)
						text += "(>= " + clock.getName() + " 0)\n";
				} else if (clock.getIndex() == counter + 1)
					text += "(>= " + clock.getName() + " 0)\n";

			text += getTransitionString(trans, counter);
			text += getDelayString(trans, smt2.getClockList(), counter);
			state = trans.getTo();
			counter++;
			text += getStateString(state, counter);
			trans = smt2.getNextTransition(state);
			text += ")\n:named S" + (counter - 1) + " ))\n\n";
		}
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

		text += "(set-option :print-success false)\n";
		text += "(set-option :produce-interpolants true)\n";
		if (logic == null)
			logic = "QF_UFLRA";

		if (logic != null)
			text += "(set-logic " + logic + ")\n\n";

		// int count = smt2.getTransitionList().size();
		List<ClockSmt2> clockList = smt2.getClockList();
		text += getDefineClockList(clockList);
		text += getDeclareVariables();

		// text += getPositiveClock(clockList, count);

		// text += super.getPositiveClockList(clockList);
		text += getDefineVariables();
		// text += getDelayBoundary(clockList, count);
		text += getTrace(smt2);

		text += getCommand();
		return text;
	}
}
