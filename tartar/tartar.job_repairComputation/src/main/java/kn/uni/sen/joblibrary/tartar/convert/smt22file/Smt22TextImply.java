package kn.uni.sen.joblibrary.tartar.convert.smt22file;

import java.util.List;

import kn.uni.sen.joblibrary.tartar.convert.smt2.model.ClockSmt2;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.ConstraintSmt2;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.ModelSmt2;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.TextSmt2;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.VariableSmt2;
import kn.uni.sen.jobscheduler.common.model.JobContext;

public class Smt22TextImply extends Smt22Text
{
	ConstraintSmt2 property;

	class Smt22TextForall extends Smt22TextFunction
	{
		public Smt22TextForall(JobContext context)
		{
			super(false, context);
		}

		String getParameter(List<ClockSmt2> clockList, int nodeCount)
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
		public String transform(ModelSmt2 smt2)
		{
			this.smt2 = smt2;
			if (smt2 == null)
				return null;

			int count = smt2.getTransitionList().size();
			List<ClockSmt2> clockList = smt2.getClockList();

			for (ClockSmt2 clock : clockList)
				clock.setConvertName("p" + clock.getOrigin());

			String text = "(assert (forall (" + getParameter(clockList, count);
			text += ") (=> (and\n";

			text += getInitialClock(clockList);
			// text += getPositiveClockList(clockList);
			text += getDefineVariables();
			text += getDelayBoundary(clockList, count);
			text += getTrace(smt2);
			text += ") ; and\n";
			text += "(not " + changeName(property).getTextSmt2() + ")";
			text += ") ; imply\n";
			text += ") ; forall\n";
			text += ") ; assert\n\n";

			return text;
		}

		private TextSmt2 changeName(TextSmt2 smt2)
		{
			// ugly, better parse input constraint and find corresponding
			// variables in variable declarations
			if (smt2 instanceof ConstraintSmt2)
			{
				ConstraintSmt2 con = (ConstraintSmt2) smt2;
				for (int i = 0; i < con.getConSize(); i++)
				{
					TextSmt2 conChild = con.getCon(i);
					if (conChild instanceof VariableSmt2)
					{
						VariableSmt2 var = (VariableSmt2) conChild;
						var.setOrigin("p" + var.getOrigin());
					}
					changeName(conChild);
				}
			}
			return smt2;
		}
	}

	@Override
	public String assertSoftText(String val)
	{
		if (val == null)
			return "";
		return "(assert-soft " + val + ")\n";
	}

	public Smt22TextImply(boolean command, ConstraintSmt2 property, JobContext context)
	{
		super(false, command, context);
		variant = "; output analysis without optimizations\n";
		fileExtra = "_imply";
		this.property = property;
	}

	public String transform(ModelSmt2 smt2)
	{
		this.smt2 = smt2;
		if (smt2 == null)
		{
			System.out.println("Error: Model not loaded.");
			return "";
		}

		preprocessTrace();

		String text = start;
		text += "; symbolic trace: " + smt2.getModelName() + "\n";
		text += smt2.getStartComment();
		text += variant + "\n";
		if (logic != null)
			text += "(set-logic " + logic + ")\n";

		int count = smt2.getTransitionList().size();
		List<ClockSmt2> clockList = smt2.getClockList();
		text += getDeclareVariables();
		text += getDefineVariables();
		text += getDefineClockList(clockList);
		text += getInitialClock(clockList);
		// text += getPositiveClockList(clockList);
		text += getDelayBoundary(clockList, count);

		text += getTrace(smt2);

		Smt22TextForall convert = new Smt22TextForall(jobContext);
		text += convert.transform(smt2);

		text += getCommand();
		text += getModel(clockList, count);

		return text;
	}

}
