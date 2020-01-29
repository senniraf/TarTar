package kn.uni.sen.joblibrary.tartar.convert.smt22file;

import java.util.ArrayList;
import java.util.List;

import kn.uni.sen.jobscheduler.common.model.RunContext;
import kn.uni.sen.joblibrary.tartar.convert.Transformer;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.ClockSmt2;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.ConstraintSmt2;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.ModelSmt2;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.TextSmt2;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.TransitionSmt2;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.ConstraintSmt2.Design;

public class Smt22TextSingleAssert extends Smt22Text
{
	public static String VarDeclaration = "";
	ConstraintSmt2 property;

	public Smt22TextSingleAssert(boolean command, ConstraintSmt2 propConstraint, RunContext context)
	{
		super(false, command, context);
		variant = "; single assert\n";
		fileExtra = "_sa";
		t0Name = "p" + Transformer.t0Name;
	}

	String getPositiveClock(List<ClockSmt2> clockList, int nodeCount)
	{
		String text = "";
		int index = 1;
		// every di delay variable is > 0
		for (ClockSmt2 clock : clockList)
		// if (1 == 1) // clock.getOrigin().compareTo(t0Name) != 0)
		{
			if (index != clock.getIndex())
			{
				index = clock.getIndex();
				text += "\n";
			}
			text += "(" + clock.getName() + " Real)";
		} // else
			// VarDeclaration += "(" + clock.getName() + " Real)";
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

	protected ClockSmt2 getClock(ConstraintSmt2 con)
	{
		for (int i = 0; i < con.getConSize(); i++)
		{
			TextSmt2 t = con.getCon(i);
			if (t instanceof ClockSmt2)
				return (ClockSmt2) t;
		}
		return null;
	}

	protected String getDelayString(TransitionSmt2 trans, List<ClockSmt2> clockList, int zoneCounter)
	{
		if (!!!substitute)
			return super.getDelayString(trans, clockList, zoneCounter);

		String text = comment(1, "; delay " + zoneCounter + " \n");

		for (ConstraintSmt2 con : trans.getConstraintList())
		{
			if (con.getDesign() == Design.DELAY)
			{
				if (con.getOperator().compareTo("ite") == 0)
				{
					substitute = false;
					return super.getDelayString(trans, clockList, zoneCounter);
				}

				// text += assertText(con.getTextSmt2());
				// System.out.println(con.getTextSmt2());
				ClockSmt2 clock = getClock(con);
				String tNew = clock.getClockValue();
				tNew = "(= " + clock.getName() + " " + tNew + ")";
				/*
				 * todo: delete if(text.contains("0)")) { checkLastClock(); }
				 * System.out.println(assertText(con.getTextSmt2()));
				 */
			}
		}
		return text + "\n";
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
		text += "(not(exists\n";
		text += "(\n";

		// only eliminate the clock delays
		if (substitute)
		{
			List<ClockSmt2> clockDelayList = new ArrayList<>();
			for (ClockSmt2 clock : smt2.getClockList())
			{
				if (clock.getOrigin().startsWith(Transformer.t0Name))
					clockDelayList.add(clock);
			}
			text += getPositiveClock(clockDelayList, count);
		} else
			text += getPositiveClock(smt2.getClockList(), count);

		text += ")\n(and\n";

		text += getInitialClock(clockList);
		// text += super.getPositiveClockList(clockList);
		text += getDefineVariables();
		text += getDelayBoundary(clockList, count);
		text += getTrace(smt2);
		if (property != null)
			text += property.getTextSmt2();

		text += ") ; and\n";

		text += ") ; not\n";
		text += ") ; exists\n";
		text += ") ; assert\n\n";

		text += getCommand();
		return text;
	}
}
