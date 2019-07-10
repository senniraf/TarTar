package kn.uni.sen.tartar.uppaal2smt2.smt22file;

import java.util.ArrayList;
import java.util.List;

import kn.uni.sen.tartar.uppaal2smt2.SMT2_OPTION;
import kn.uni.sen.tartar.uppaal2smt2.Transformer;
import kn.uni.sen.tartar.uppaal2smt2.smt2.model.ClockSmt2;
import kn.uni.sen.tartar.uppaal2smt2.smt2.model.ConstraintSmt2;
import kn.uni.sen.tartar.uppaal2smt2.smt2.model.ModelSmt2;
import kn.uni.sen.tartar.uppaal2smt2.smt2.model.TextSmt2;
import kn.uni.sen.tartar.uppaal2smt2.smt2.model.TransitionSmt2;
import kn.uni.sen.tartar.uppaal2smt2.smt2.model.ConstraintSmt2.Design;

public class Smt22TextElimination extends Smt22Text
{
	public static String VarDeclaration = "";
	ConstraintSmt2 property;

	public Smt22TextElimination(boolean command, ConstraintSmt2 property, SMT2_OPTION option)
	{
		super(false, command);
		if (option != SMT2_OPTION.RESET)
			substitute = true;
		variant = "; output quantifier elimination\n";
		fileExtra = "_qe";
		this.property = property;
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
	public String transform(ModelSmt2 smt2, int commentDepth)
	{
		this.smt2 = smt2;
		this.commentDepth = commentDepth;
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
		text += "(forall\n";
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

		text += ")\n(=> (and\n";

		text += getInitialClock(clockList);
		//text += super.getPositiveClockList(clockList);
		text += getDefineVariables();
		text += getDelayBoundary(clockList, count);
		text += getTrace(smt2);

		text += ") ; and\n";

		String prop = "false";
		if (property != null)
			prop = property.getTextSmt2();
		text += prop; // "(not " + prop + ")";
		text += ") ; =>\n";
		text += ") ; exists\n";
		text += ") ; assert\n\n";

		text += getCommand();
		return text;
	}
}
