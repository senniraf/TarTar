package kn.uni.sen.tartar.uppaal2smt2.uppaaltrace.model;

import java.util.ArrayList;
import java.util.List;

public class VariableVector
{
	String id;
	List<VariableState> varList = new ArrayList<>();

	public VariableVector(String id)
	{
		this.id = id;
	}

	public String getID()
	{
		return id;
	}

	public void addVariableState(VariableState var)
	{
		varList.add(var);
	}

	public List<VariableState> getVariableList()
	{
		return varList;
	}
}
