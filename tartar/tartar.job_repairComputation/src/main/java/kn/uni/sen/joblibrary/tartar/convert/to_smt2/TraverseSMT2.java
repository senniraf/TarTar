package kn.uni.sen.joblibrary.tartar.convert.to_smt2;

import java.util.List;

import kn.uni.sen.joblibrary.tartar.convert.Transformer;
import kn.uni.sen.joblibrary.tartar.convert.Ut2Smt2;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.ClockSmt2;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.ConstantSmt2;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.ConstraintSmt2;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.ModelSmt2;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.StateSmt2;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.TransitionSmt2;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.VariableSmt2;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.ConstraintSmt2.Design;

/**
 * Traverses smt2 model and calls creator for smt2-file or smt2-api
 * 
 * @author Martin Koelbl
 */
public class TraverseSMT2
{
	protected final static String startComment = "; UPPAAL symbolic trace to smt2 translation (Version "
			+ Ut2Smt2.version + ")\n";
	final String t0Name = Transformer.t0Name;

	ModelSmt2 smt2;
	String logic;
	String variant = "";

	CreateSMT2 creator;

	public TraverseSMT2(CreateSMT2 creator)
	{
		// variant = "; by extra model\n";
		this.creator = creator;
	}

	protected void addConstraint(ConstraintSmt2 con)
	{
		creator.addFormula(con);
	}

	public void setLogic(String logic)
	{
		this.logic = logic;
	}

	void defineVariable(String op, String name, String val)
	{
		ConstraintSmt2 con = new ConstraintSmt2(op);
		con.addCon(new ConstantSmt2(name));
		con.addCon(new ConstantSmt2(val));
		addConstraint(con);
	}

	protected void getDeclareVariables()
	{
		creator.addComment(1, "declare local variables");
		List<VariableSmt2> varList = smt2.getAllVariableList();
		if (varList.isEmpty())
			return;
		for (VariableSmt2 var : varList)
		{
			creator.createVariable(var.getName(), var.getType());
		}
		creator.addNewLine();
	}

	protected void getDefineVariables()
	{
		List<VariableSmt2> varList = smt2.getAllVariableList();
		if (varList.isEmpty())
			return;
		creator.addComment(1, "define local variables");
		for (VariableSmt2 var : varList)
		{
			String val = var.defineValue();
			if (val == null)
				continue;
			defineVariable("=", var.getName(), var.getValue());
		}
		creator.addNewLine();
	}

	protected void getDefineClockList(List<ClockSmt2> clockList)
	{
		creator.addComment(1, "declare clocks");
		int index = 1;
		for (ClockSmt2 clock : clockList)
		{
			if (index != clock.getIndex())
			{
				index = clock.getIndex();
			}
			creator.createVariable(clock.getName(), "Real");
		}
		creator.addNewLine();
	}

	protected void getPositiveClockList(List<ClockSmt2> clockList)
	{
		creator.addComment(1, "clocks are always positive");
		int index = 2;
		for (ClockSmt2 clock : clockList)
		{
			if (clock.getOrigin().compareTo(t0Name) == 0)
				continue;
			if (clock.getIndex() == 1)
				continue;

			if (index != clock.getIndex())
			{
				index = clock.getIndex();
			}
			defineVariable(">=", clock.getName(), "0.0");
		}
		creator.addNewLine();
	}

	protected void getInitialClock(List<ClockSmt2> clockList)
	{
		creator.addComment(1, "initial clock values");
		for (ClockSmt2 clock : clockList)
		{
			if (clock.getOrigin().compareTo(t0Name) == 0)
				continue;
			if (clock.getIndex() != 1)
				continue;

			// every start clock is zero
			defineVariable("=", clock.getName(), "0.0");
		}
		creator.addNewLine();
	}

	protected void getDelayBoundary(List<ClockSmt2> clockList, int maxStep)
	{
		creator.addComment(1, "delays are always positive");
		for (ClockSmt2 clock : clockList)
		{
			if (clock.getOrigin().compareTo(t0Name) != 0)
				continue;

			// every di delay variable is >= 0
			defineVariable(">=", clock.getName(), "0.0");
		}
		creator.addNewLine();
	}

	protected void getStateString(StateSmt2 state, int zoneCounter)
	{
		creator.addComment(1, "; symbolic state " + zoneCounter + "\n");
		// String com1 = "; zone " + zoneCounter + "\n";
		if (state.isUrgent())
		{
			creator.addComment(2, "; is urgent \n");
		}
		for (ConstraintSmt2 con : state.getConstraintList())
		{
			addConstraint(con);
			if (con.getDesign() != Design.UNKOWN)
				creator.addComment(3, "; " + con.getDesign() + "\n");
		}
		for (VariableSmt2 var : state.getVariableList())
		{
			if (var.getClass() == ClockSmt2.class)
				continue;
			if (var.getValue() != null)
				defineVariable("=", var.getName(), var.getValue());
		}
		creator.addNewLine();
	}

	String getTransitionFromToString(TransitionSmt2 trans)
	{
		return trans.getFromName() + " -> " + trans.getToName();
	}

	protected void getTransitionString(TransitionSmt2 trans, int zoneCounter)
	{
		creator.addComment(1, "transition " + zoneCounter + "");
		creator.addComment(2, "\n" + getTransitionFromToString(trans));
		for (ConstraintSmt2 con : trans.getConstraintList())
		{
			if (con.getDesign() == Design.DELAY)
				continue;

			addConstraint(con);
			if (con.getDesign() != Design.UNKOWN)
				creator.addComment(3, "" + con.getDesign());
		}
		creator.addNewLine();
	}

	protected void getDelayString(TransitionSmt2 trans, List<ClockSmt2> clockList, int zoneCounter)
	{
		creator.addComment(1, "delay " + zoneCounter);

		for (ConstraintSmt2 con : trans.getConstraintList())
		{
			if (con.getDesign() == Design.DELAY)
				addConstraint(con);
		}
		creator.addNewLine();
	}

	protected void getTrace(ModelSmt2 smt2)
	{
		StateSmt2 state = smt2.getInitialState();
		TransitionSmt2 trans = smt2.getNextTransition(state);
		int counter = 1;
		getStateString(state, counter);
		while (trans != null)
		{
			getTransitionString(trans, counter);
			getDelayString(trans, smt2.getClockList(), counter);
			state = trans.getTo();
			counter++;
			getStateString(state, counter);
			trans = smt2.getNextTransition(state);
		}
	}

	public String getCommand()
	{
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
		String text = "(echo \"--- doing get-model\")\n";
		text += "(get-model) \n";
		text += "(get-value (\n";

		text += getModelContent(clockList, maxStep);
		text += "))\n";
		return text;
	}

	public void transform(ModelSmt2 smt2, int commentDepth)
	{
		this.smt2 = smt2;
		if (smt2 == null)
		{
			System.out.println("Error: Model not loaded.");
			return;
		}
		if (creator == null)
		{
			System.out.println("Error: SMT2 output creator is missing.");
			return;
		}

		preprocessTrace();

		creator.addComment(1, startComment);
		creator.addComment(1, "; symbolic trace: " + smt2.getModelName() + "\n");
		creator.addComment(1, smt2.getStartComment());
		creator.addComment(1, variant + "\n");
		if (logic != null)
			creator.addOption("set-logic", logic);

		createModel();

		// getModel(clockList, count);
		creator.finish();
	}

	protected void createModel()
	{
		int count = smt2.getTransitionList().size();
		List<ClockSmt2> clockList = smt2.getClockList();
		getDeclareVariables();
		getDefineVariables();
		getDefineClockList(clockList);
		getInitialClock(clockList);
		getPositiveClockList(clockList);
		getDelayBoundary(clockList, count);

		getTrace(smt2);
		getCommand();
	}

	protected void preprocessTrace()
	{
	}
	/*
	 * public String declarationText(String name, String type, boolean function)
	 * { String decl = "const"; if (function) decl = "fun"; return "(declare-" +
	 * decl + " " + name + " " + type + ")\n"; }
	 * 
	 * public String assertText(String val) { if (val == null) return ""; return
	 * "(assert " + val + ")\n"; }
	 * 
	 * public String assertSoftText(String val) { if (val == null) return "";
	 * return "(assert-soft " + val + ")\n"; }
	 */
}
