package kn.uni.sen.joblibrary.tartar.convert.smt22file;

import java.util.ArrayList;
import java.util.List;

import kn.uni.sen.jobscheduler.common.model.RunContext;
import kn.uni.sen.joblibrary.tartar.convert.Transformer;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.ClockSmt2;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.ConstraintSmt2;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.ModelSmt2;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.StateSmt2;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.TransitionSmt2;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.VariableSmt2;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.ConstraintSmt2.Design;

/**
 * Writes smt2 model to a file.
 * 
 * @author Martin Koelbl
 */
public class Smt22Text extends Transformer
{
	ModelSmt2 smt2;
	boolean command;

	String logic;

	public static boolean substitute = false;

	public String t0Name = Transformer.t0Name;

	public Smt22Text(boolean bdm, boolean command, RunContext context)
	{
		super(context);
		substitute = false;
		// variant = "; by extra model\n";
		this.command = command;
		if (bdm)
			fileExtra = "_bdm";
		else
			fileExtra = "";
	}

	public void setLogic(String logic)
	{
		this.logic = logic;
	}

	protected String getDeclareVariables()
	{
		String text = comment(1, "; declare local variables\n");
		List<VariableSmt2> varList = smt2.getAllVariableList();
		if (varList.isEmpty())
			return "";
		// todo: hack since some variable are declared not only once
		List<String> nameList = new ArrayList<>();
		for (VariableSmt2 var : varList)
		{
			if (containList(nameList, var.getName()))
				continue;
			text += declarationText(var.getName(), var.getType(), false, var.getComment());
			nameList.add(var.getName());
		}
		return text + "\n";
	}

	private boolean containList(List<String> nameList, String name)
	{
		for (String n : nameList)
			if (n.compareTo(name) == 0)
				return true;
		return false;
	}

	protected String getDefineVariables()
	{
		String text = comment(1, "; define local variables\n");
		List<VariableSmt2> varList = smt2.getAllVariableList();
		if (varList.isEmpty())
			return "";
		for (VariableSmt2 var : varList)
		{
			String val = var.defineValue();
			if (val == null)
				continue;
			text += assertText(val);
		}
		return text + "\n";
	}

	protected String getDefineClockList(List<ClockSmt2> clockList)
	{
		String text = comment(1, "; declare clocks\n");
		int index = 1;
		for (ClockSmt2 clock : clockList)
		{
			if (index != clock.getIndex())
			{
				index = clock.getIndex();
				text += "\n";
			}
			text += declarationText(clock.getName(), "Real", false, null);
		}
		return text + "\n";
	}

	/*
	 * protected String getPositiveClockList(List<ClockSmt2> clockList) { String
	 * text = comment(1, "; clocks are always positive\n"); int index = 2; for
	 * (ClockSmt2 clock : clockList) { if (clock.getOrigin().compareTo(t0Name)
	 * == 0) continue; if (clock.getIndex() == 1) continue;
	 * 
	 * if (index != clock.getIndex()) { index = clock.getIndex(); text += "\n";
	 * } // every di delay variable is >= 0 text += assertText("(>= " +
	 * clock.getName() + " 0)"); } return text + "\n"; }
	 */

	protected String getInitialClock(List<ClockSmt2> clockList)
	{
		String text = comment(1, "; initial clock values \n");
		for (ClockSmt2 clock : clockList)
		{
			if (clock.getOrigin().compareTo(t0Name) == 0)
				continue;
			if (clock.getIndex() != 1)
				continue;

			// every start clock is zero
			text += assertText("(= " + clock.getName() + " 0)");
		}
		text += "\n";
		return text;
	}

	protected String getDelayBoundary(List<ClockSmt2> clockList, int maxStep)
	{
		String text = comment(1, "; delays are always positive\n");
		for (ClockSmt2 clock : clockList)
		{
			if (clock.getOrigin().compareTo(t0Name) != 0)
				continue;

			// every di delay variable is >= 0
			text += assertText("(>= " + clock.getName() + " 0)");
		}
		return text + "\n";
	}

	protected String getVariableDeclaration(VariableSmt2 varSmt2)
	{
		return declarationText(varSmt2.getName(), varSmt2.getType(), false, null);
	}

	protected String getStateString(StateSmt2 state, int zoneCounter)
	{
		String com1 = "; symbolic state " + zoneCounter + "\n";
		// String com1 = "; zone " + zoneCounter + "\n";
		String text = "";
		String com2 = "";
		if (state.isUrgent())
		{
			com2 += "; is urgent\n";
		}
		for (ConstraintSmt2 con : state.getConstraintList())
		{
			// System.out.println(con.getTextSmt2());
			if (con.isSoft())
				text += assertSoftText(con.getTextSmt2());
			else
				text += assertText(con.getTextSmt2());
			if (con.getDesign() != Design.UNKOWN)
				text += "; " + con.getDesign() + "\n";
		}
		for (VariableSmt2 var : state.getVariableList())
		{
			if (var.getClass() == ClockSmt2.class)
				continue;
			text += assertText(var.defineValue());
		}

		text = comment(1, com1) + comment(2, com2) + text;
		return text + "\n";
	}

	String getTransitionFromToString(TransitionSmt2 trans)
	{
		return trans.getFromName() + " -> " + trans.getToName();
	}

	protected String getTransitionString(TransitionSmt2 trans, int zoneCounter)
	{
		String text = comment(1, "; transition " + zoneCounter + "\n");
		text += comment(2, "; " + getTransitionFromToString(trans) + "\n");
		for (ConstraintSmt2 con : trans.getConstraintList())
		{
			if (con.getDesign() == Design.DELAY)
				continue;

			if (con.isSoft())
				text += assertSoftText(con.getTextSmt2());
			else
				text += assertText(con.getTextSmt2());
			if (con.getDesign() != Design.UNKOWN)
				text += "; " + con.getDesign() + "\n";
		}
		return text + "\n";
	}

	protected String getDelayString(TransitionSmt2 trans, List<ClockSmt2> clockList, int zoneCounter)
	{
		String text = comment(1, "; delay " + zoneCounter + " \n");

		for (ConstraintSmt2 con : trans.getConstraintList())
		{
			if (con.getDesign() == Design.DELAY)
			{
				text += assertText(con.getTextSmt2());
				/*
				 * todo: delete if(text.contains("0)")) { checkLastClock(); }
				 * System.out.println(assertText(con.getTextSmt2()));
				 */
			}
		}
		return text + "\n";
	}

	protected String getTrace(ModelSmt2 smt2)
	{
		String text = "";
		StateSmt2 state = smt2.getInitialState();
		TransitionSmt2 trans = smt2.getNextTransition(state);
		int counter = 1;
		text += getStateString(state, counter);
		while (trans != null)
		{
			text += getTransitionString(trans, counter);
			text += getDelayString(trans, smt2.getClockList(), counter);
			state = trans.getTo();
			counter++;
			text += getStateString(state, counter);
			trans = smt2.getNextTransition(state);
		}
		return text;
	}

	public String getCommand()
	{
		if (!!!command)
			return "";

		String text = "(echo \"--- doing check-sat\")\n";
		text += "(check-sat)\n\n";
		return text;
	}

	protected String getModelContent(List<ClockSmt2> clockList, int nodeCount)
	{
		String text = "";
		String textDelay = "";
		String textExtra = "";

		for (ClockSmt2 clock : clockList)
		{
			if (clock.getName().startsWith(t0Name))
			{
				textDelay += clock.getName() + "\n";
				continue;
			}

			if (clock.isExtra())
			{
				textExtra += clock.getName() + "\n";
				continue;
			}

			int index = clock.getIndex();
			text += clock.getName() + " (+ " + clock.getName() + " " + t0Name + index + ")\n";
		}

		for (VariableSmt2 var : smt2.getAllVariableList())
			text += var.getName() + "\n";
		return text + textDelay + textExtra;
	}

	protected String getModel(List<ClockSmt2> clockList, int maxStep)
	{
		if (!!!command)
			return "";
		String text = "(echo \"--- doing get-model\")\n";
		text += "(get-model) \n";
		text += "(get-value (\n";

		text += getModelContent(clockList, maxStep);
		text += "))\n";
		return text;
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
		text += getCommand();

		text += getModel(clockList, count);

		return text;
	}

	protected void preprocessTrace()
	{
	}

	public String declarationText(String name, String type, boolean function, String com)
	{
		String decl = "const";
		if (function)
			decl = "fun";
		if ((com == null) || (com.replace(" ", "").isEmpty()))
			com = "";
		else
			com = ";" + com;
		return "(declare-" + decl + " " + name + " " + type + ")" + com + "\n";
	}

	public String assertText(String val)
	{
		if (val == null)
			return "";
		return "(assert " + val + ")\n";
	}

	public String assertSoftText(String val)
	{
		if (val == null)
			return "";
		return "(assert-soft " + val + ")\n";
	}
}
