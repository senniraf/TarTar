package kn.uni.sen.tartar.uppaal2smt2.smt2.model;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

public class TransitionSmt2
{
	String name;
	StateSmt2 from;
	StateSmt2 to;
	List<ClockSmt2> resetList;
	List<ConstraintSmt2> constraintList = new LinkedList<ConstraintSmt2>();
	String fromName = "";
	String toName = "";

	public TransitionSmt2(String name, StateSmt2 from, StateSmt2 to)
	{
		this.name = name;
		this.from = from;
		this.to = to;
	}

	public String getName()
	{
		return name;
	}

	public void addReset(ClockSmt2 clock)
	{
		if (resetList == null)
			resetList = new ArrayList<>();
		resetList.add(clock);
	}

	public boolean isReset(ClockSmt2 reset)
	{
		if (reset == null)
			return false;
		if (resetList == null)
			return false;
		for (ClockSmt2 clock : resetList)
		{
			if (reset == clock)
				return true;
			if (reset.getName().compareTo(clock.getName()) == 0)
				return true;
		}
		return false;
	}

	public StateSmt2 getFrom()
	{
		return from;
	}

	public StateSmt2 getTo()
	{
		return to;
	}

	public void addConstraint(ConstraintSmt2 con)
	{
		constraintList.add(con);
	}

	public List<ConstraintSmt2> getConstraintList()
	{
		return constraintList;
	}

	public void addFromName(String from)
	{
		if (!!!fromName.isEmpty())
			return;
		fromName = from;
	}

	public void addToName(String to)
	{
		if (!!!toName.isEmpty())
			return;
		toName = to;
	}

	public String getFromName()
	{
		return fromName;
	}

	public String getToName()
	{
		return toName;
	}

	public ClockSmt2 getClock(String origin, int i)
	{
		VariableSmt2 var = from.getVariableByName(ClockSmt2.getName(origin, i, null));
		if (var == null)
			var = to.getVariableByName(ClockSmt2.getName(origin, i, null));
		if (var == null)
			return null;
		if (var instanceof ClockSmt2)
			return (ClockSmt2) var;
		return null;
	}

	public List<ClockSmt2> getResetList()
	{
		return resetList;
	}
}
