package kn.uni.sen.tartar.uppaal2smt2.smt22file;

import java.util.List;

import kn.uni.sen.tartar.uppaal2smt2.Transformer;
import kn.uni.sen.tartar.uppaal2smt2.smt2.model.ClockSmt2;
import kn.uni.sen.tartar.uppaal2smt2.smt2.model.ConstraintSmt2;
import kn.uni.sen.tartar.uppaal2smt2.smt2.model.ModelSmt2;

public class Smt22TextFunctionImply extends Smt22TextFunction
{
	ConstraintSmt2 property;
	String assertSoftText = "";

	public Smt22TextFunctionImply(boolean command, ConstraintSmt2 property)
	{
		super(command);
		variant = "; output function with imply\n";
		fileExtra = "_func";
		t0Name = "p" + Transformer.t0Name;
		this.property = property;
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
	public String assertSoftText(String val)
	{
		if (val == null)
			return "";
		assertSoftText += "(assert-soft " + val + ")\n";
		return "";
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
		text += getDefineVariables();
		String textImply = getImplyText(clockList);

		for (ClockSmt2 clock : clockList)
			clock.setConvertName("p" + clock.getOrigin());

		text += "(define-fun Pi(\n";
		text += getPositiveClock(clockList, count);
		text += ")\n Bool(and\n";

		text += getInitialClock(clockList);
		//text += getPositiveClockList(clockList);
		text += getDelayBoundary(clockList, count);
		text += getTrace(smt2);

		text += ") ; and\n";
		text += ") ; define-fun\n\n";
		text += "\n" + textImply;

		text += "\n" + assertSoftText;
		text += getCommand();
		return text;
	}

	private String getImplyText(List<ClockSmt2> clockList)
	{

		ConstraintSmt2 pi = new ConstraintSmt2("Pi");
		for (ClockSmt2 clock : clockList)
			pi.addCon(clock);

		if (property == null)
			property = new ConstraintSmt2("false");
		ConstraintSmt2 imply = new ConstraintSmt2("=>", pi, property);
		imply.setNewLine(true);

		String textAll = "(assert\n (forall(" + getPositiveClock(clockList, smt2.getTransitionList().size());
		textAll += ")\n" + imply.getTextSmt2() + ")\n)\n";

		return textAll;
	}
}
