package kn.uni.sen.tartar.uppaal2smt2.uppaaltrace.model;

public class Node
{
	String name;
	String dbmName;
	DBM dbm;
	String locVec;
	String varVec;

	public Node(String name, String locVec, String varVec, String dbmName)
	{
		this.name = name;
		this.dbmName = dbmName;
		this.locVec = locVec;
		this.varVec = varVec;
	}

	public String getName()
	{
		return name;
	}
	
	public String getLocationVector()
	{
		return locVec;
	}
	
	public String getVariableVector()
	{
		return varVec;
	}

	public String getDbmName()
	{
		return dbmName;
	}

	public void setDBM(DBM dbm)
	{
		this.dbm = dbm;
	}

	public DBM getDBM()
	{
		return dbm;
	}
}
