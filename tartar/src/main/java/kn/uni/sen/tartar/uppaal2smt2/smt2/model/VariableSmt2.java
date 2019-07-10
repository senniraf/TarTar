package kn.uni.sen.tartar.uppaal2smt2.smt2.model;

public class VariableSmt2 implements TextSmt2
{
	protected String name;
	protected String type;
	protected String value;
	protected String comment;
	protected int lastSetStep = 1; // last step this variable was set
	protected int step_index;
	protected String endName;

	// defined as const because of smt2
	protected boolean constant = false;
	// constant in uppaal
	protected boolean fix = false;

	public VariableSmt2(String name, String type, String value, int step_index, String endName)
	{
		this.name = name;
		this.type = type;
		this.value = value;
		this.step_index = step_index;
		this.endName = endName;
	}

	public void setComment(String c)
	{
		this.comment = c;
	}

	public String getComment()
	{
		return comment;
	}

	public int getIndex()
	{
		return step_index;
	}

	public String getName()
	{
		return getName(name, step_index, endName);
	}

	public String getOrigin()
	{
		return name;
	}

	public String getType()
	{
		return type;
	}

	public void setLastSetStep(int step)
	{
		lastSetStep = step;
	}

	public int getLastSetStep()
	{
		return lastSetStep;
	}

	public String getValue()
	{
		return value;
	}

	public String defineValue()
	{
		if (value == null)
			return null;
		return "(= " + getName() + " " + value + " )";
	}

	public String getTextSmt2()
	{
		return getName();
	}

	public void setConstant(boolean c)
	{
		this.constant = c;
	}

	public boolean getConstant()
	{
		return this.constant;
	}

	public void setDefine(boolean c)
	{
		this.fix = c;
	}

	public boolean getDefine()
	{
		return this.fix;
	}

	public static String getName(String origin, int step_index, String end)
	{
		if ((end == null) || end.replace(" ", "").isEmpty())
			end = "";
		else
			end = "_" + end;

		String id = "";
		if (step_index != 0)
			return origin + step_index + id + end;
		return origin + id + end;
	}

	public String getNameEnd()
	{
		return endName;
	}

	public void setOrigin(String string)
	{
		name = string;
	}

	public boolean compareName(String name2)
	{
		if (getName().compareTo(name2) == 0)
			return true;
		if (constant)
			if (getOrigin().compareTo(name2) == 0)
				return true;
		return false;
	}
}
