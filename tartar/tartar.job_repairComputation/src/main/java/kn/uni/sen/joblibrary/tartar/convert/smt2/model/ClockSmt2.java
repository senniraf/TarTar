package kn.uni.sen.joblibrary.tartar.convert.smt2.model;

import kn.uni.sen.joblibrary.tartar.convert.Transformer;

public class ClockSmt2 extends VariableSmt2
{
	protected String addValue;
	boolean extra = false;

	public ClockSmt2(String id, int step_index)
	{
		super(id, "clock", null, step_index, null);
		if (id.startsWith("sys."))
			setConvertName(id);
	}

	public void setConvertName(String name)
	{
		// convert name -> smt2 name (means delete sys. but use local name)
		if (name.startsWith("sys."))
			name = name.substring(4);

		if (name.compareTo("t(0)") == 0)
			name = Transformer.t0Name;
		this.name = name;
	}

	public void setExtra(boolean extra)
	{
		this.extra = extra;
	}

	public boolean isExtra()
	{
		return extra;
	}

	public String getClockValue()
	{
		if (getOrigin().compareTo(Transformer.t0Name) == 0)
			return getName();

		String tNew = "";
		int zoneCounter = this.getIndex();
		for (int i = this.getLastSetStep(); i < zoneCounter; i++)
		{
			tNew += Transformer.t0Name + i + " ";
		}
		if (tNew.isEmpty())
			return "0";
		else if (zoneCounter - this.getLastSetStep() == 1)
			return tNew;
		else
			return "(+ " + tNew + ")";
	}

	public void addValue(String val)
	{
		this.addValue = val;
	}
}
