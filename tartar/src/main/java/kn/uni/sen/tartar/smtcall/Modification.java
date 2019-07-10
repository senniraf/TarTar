package kn.uni.sen.tartar.smtcall;

import kn.uni.sen.tartar.uppaal2smt2.SMT2_OPTION;
import kn.uni.sen.tartar.uppaal2smt2.smt2modify.Smt2ModComparison;

/**
 * Contain change constraint
 * 
 * @author Martin Koelbl
 */
public class Modification
{
	SMT2_OPTION option;
	String assertText; // assert to ignore soft-assert
	String name;
	String valueDefault;
	String valueNew;
	int step = -2;

	int id = 0;
	int index = 0;

	public Modification(String asserttext, String name, String oldValue, String newValue)
	{
		option = getModification(name);
		assertText = asserttext;
		this.name = name;
		valueDefault = oldValue;
		valueNew = getNewValue(newValue);
	}

	private String getNewValue(String newValue)
	{
		if (option == SMT2_OPTION.COMPARISON)
		{
			String name = this.name;
			int index = name.lastIndexOf("_");
			if (index == -1)
				return "";
			String opName = name.substring(index + 1);
			if (opName == null)
				return "";
			String opNew = Smt2ModComparison.getOperation(opName);
			if (opNew != null)
				return opNew;
		}
		return newValue;
	}

	public Modification(SMT2_OPTION option, int id, int index, String newVal)
	{
		this.option = option;
		this.id = id;
		this.index = index;
		valueDefault = "";
		valueNew = newVal;
	}

	public void setID(int id, int index)
	{
		this.id = id;
		this.index = index;
	}

	public int getID()
	{
		return id;
	}

	public int getIndex()
	{
		return index;
	}

	public static SMT2_OPTION getModification(String name)
	{
		for (SMT2_OPTION opt : SMT2_OPTION.ListModifier)
		{
			if (name.startsWith("_" + SMT2_OPTION.getName(opt)))
				return opt;
		}
		return null;
	}

	public SMT2_OPTION getOption()
	{
		return option;
	}

	public void setDefaultValue(String d)
	{
		valueDefault = d;
	}

	public String getAssertText()
	{
		return assertText;
	}

	public String getName()
	{
		return name;
	}

	public String getValueDefault()
	{
		return valueDefault;
	}

	public String getValueNew()
	{
		return valueNew;
	}

	/*
	 * public int getLabelID() { if (step != -2) return step; if (name == null)
	 * return -1; int index = name.lastIndexOf("_"); if (index < 0) return -1;
	 * String s = name.substring(index + 1); try { step = Integer.parseInt(s); }
	 * catch (Exception ex) { step = -1; } return step; }
	 */

	public boolean isEquivalent(Modification other)
	{
		if (name.compareTo(other.getName()) != 0)
			return false;
		if (valueNew.compareTo(other.getValueNew()) != 0)
			return false;
		return true;
	}

	public void setNewValue(String valNew)
	{
		// comparison is set by modification name
		if (option == SMT2_OPTION.COMPARISON)
			return;
		valueNew = valNew;
	}
}
