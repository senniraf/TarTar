package kn.uni.sen.tartar.uppaal2smt2.uppaaltrace.model;

public class VariableState
{
	String id;
	String value;

	public VariableState(String id, String value)
	{
		this.id = id;
		this.value = value;
	}

	public String getID()
	{
		return id;
	}

	public String getValue()
	{
		return value;
	}
}
