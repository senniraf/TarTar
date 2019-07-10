package kn.uni.sen.tartar.uppaal2smt2.smt2.model;

import java.util.ArrayList;
import java.util.List;

import kn.uni.sen.tartar.uppaal2smt2.smt22file.Smt22Text;

public class ConstraintSmt2 implements TextSmt2
{
	public enum Design
	{
		UNKOWN, DELAY, URGENT, GUARD, INVARIANT, UPDATE
	}

	// (+ x1 1)
	// (>= x1 0)
	// (>= (+ x1 1) (+ x2 1))
	String operator;
	// contains a
	Design design = Design.UNKOWN;

	int id = 0;
	int idL = 0;
	int idModel = 0;

	List<TextSmt2> conList = new ArrayList<>();

	// is this constraint a soft assert
	boolean soft;
	boolean newLine;

	public void setDesign(Design design)
	{
		this.design = design;
	}

	public Design getDesign()
	{
		return design;
	}

	public void setNewLine(boolean b)
	{
		this.newLine = b;
	}

	public boolean getNewLine()
	{
		return newLine;
	}

	public ConstraintSmt2(String op)
	{
		operator = op;
	}

	public ConstraintSmt2(String op, TextSmt2 con1)
	{
		operator = op;
		conList.add(con1);
	}

	public ConstraintSmt2(String op, TextSmt2 con1, TextSmt2 con2)
	{
		operator = op;
		conList.add(con1);
		conList.add(con2);
	}

	public ConstraintSmt2(String op, TextSmt2 con1, TextSmt2 con2, TextSmt2 con3)
	{
		operator = op;
		conList.add(con1);
		conList.add(con2);
		conList.add(con3);
	}

	public String getOperator()
	{
		return operator;
	}

	public TextSmt2 getCon(int index)
	{
		if (conList.size() <= index)
			return null;
		return conList.get(index);
	}

	public int getConSize()
	{
		return conList.size();
	}

	public void addCon(TextSmt2 con)
	{
		conList.add(con);
	}

	public void setSoft(boolean soft)
	{
		this.soft = soft;
	}

	public boolean isSoft()
	{
		return soft;
	}

	/*
	 * public String getTextSmt2() { String text = "(" + operator; for (TextSmt2
	 * con : conList) text += " " + con.getTextSmt2() + (newLine ? "\n  " : "");
	 * return text + ")"; }
	 */

	public String getTextSmt2()
	{
		String text = "(" + operator;
		for (TextSmt2 con : conList)
		{
			text += " ";
			String newT = con.getTextSmt2();
			if (Smt22Text.substitute && (con instanceof ClockSmt2))
				newT = ((ClockSmt2) con).getClockValue();
			text += newT + (newLine ? "\n  " : "");
		}
		return text + ")";
	}

	public void setOperator(String op)
	{
		operator = op;
	}

	public void setIndex(int index, VariableSmt2 variableSmt2)
	{
		conList.remove(index);
		conList.add(index, variableSmt2);
	}

	public void setID(int id)
	{
		this.id = id;
	}

	public int getID()
	{
		return id;
	}

	public void setIDL(int idL)
	{
		this.idL = idL;
	}

	public int getIDL()
	{
		return idL;
	}

	public void setIDModel(int idModel)
	{
		this.idModel = idModel;
	}

	public int getIDModel()
	{
		return idModel;
	}
}
