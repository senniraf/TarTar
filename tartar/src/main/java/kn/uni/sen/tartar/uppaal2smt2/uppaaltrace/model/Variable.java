package kn.uni.sen.tartar.uppaal2smt2.uppaaltrace.model;

public class Variable
{
	String name;
	String id;

	public Variable(String name, String id)
	{
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
