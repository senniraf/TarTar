package kn.uni.sen.joblibrary.tartar.convert.uppaaltrace.model;

import kn.uni.sen.joblibrary.tartar.convert.Trace2Smt2ByBDM;

public class Clock
{
	String name;
	String id;

	public Clock(String name, String id)
	{
		if (name.compareTo("t(0)") == 0)
			name = Trace2Smt2ByBDM.t0Name;
		this.name = name;
		this.id = id;
	}

	public String getName()
	{
		return name;
	}

	public String getID()
	{
		return id;
	}
}
