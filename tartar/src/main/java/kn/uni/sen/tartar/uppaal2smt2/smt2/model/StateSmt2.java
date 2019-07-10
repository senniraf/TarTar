package kn.uni.sen.tartar.uppaal2smt2.smt2.model;

import java.util.ArrayList;
import java.util.List;

public class StateSmt2
{
	String[] locationList = { "" };
	boolean urgent;
	int index = -1;
	int stateID = -1;
	// index of state and transition in uppaal file
	List<Integer> uppaalIDList = new ArrayList<>();
	List<ConstraintSmt2> constraintList = new ArrayList<ConstraintSmt2>();
	List<VariableSmt2> variableList = new ArrayList<VariableSmt2>();

	public StateSmt2(int index)
	{
		this.index = index;
	}

	public int getIndex()
	{
		return index;
	}

	public void setName(String name)
	{
		locationList = new String[] { name };
	}

	public String getName()
	{
		if (locationList.length > 0)
			return locationList[0];
		return "";
	}

	public void setLocationList(String[] list)
	{
		locationList = list;
	}

	public void addConstraint(ConstraintSmt2 con)
	{
		constraintList.add(con);
	}

	public List<ConstraintSmt2> getConstraintList()
	{
		return constraintList;
	}

	public void addVariable(VariableSmt2 con)
	{
		variableList.add(con);
	}

	public List<VariableSmt2> getVariableList()
	{
		return variableList;
	}

	public VariableSmt2 getVariableByName(String name)
	{
		for (VariableSmt2 var : variableList)
			if (var.getName().compareTo(name) == 0)
				return var;
		return null;
	}

	public VariableSmt2 getVariableByOrigin(String orgName)
	{
		for (VariableSmt2 var : variableList)
			if (var.getOrigin().compareTo(orgName) == 0)
				return var;
		return null;
	}

	public void addClock(ClockSmt2 clock)
	{
		variableList.add(clock);
	}

	public List<ClockSmt2> getClockList()
	{
		List<ClockSmt2> clockList = new ArrayList<ClockSmt2>();
		for (VariableSmt2 var : variableList)
			if ((var.getType() != null) && (var.getType().compareTo("clock") == 0))
				clockList.add((ClockSmt2) var);
		return clockList;
	}

	// public ClockSmt2 getClockByName(String name)
	// {
	// for (ClockSmt2 clock : clockList)
	// if (clock.getName().compareTo(name) == 0)
	// return clock;
	// return null;
	// }

	public void setUrgent(boolean urgent)
	{
		this.urgent = urgent;
	}

	public boolean isUrgent()
	{
		return urgent;
	}

	public ClockSmt2 getClock(String name)
	{
		VariableSmt2 var = getVariableByName(name);
		if (var instanceof ClockSmt2)
			return (ClockSmt2) var;
		return null;

	}

	public ClockSmt2 getClock(String origin, int step_index)
	{
		return getClock(VariableSmt2.getName(origin, step_index, null));
	}

	/*
	 * public void setID(int stateID) { this.stateID = stateID; }
	 * 
	 * public int getID() { return stateID; }
	 */

	public void addUppaalID(int id)
	{
		uppaalIDList.add(id);
	}

	public List<Integer> getUppaalID()
	{
		return uppaalIDList;
	}
}
