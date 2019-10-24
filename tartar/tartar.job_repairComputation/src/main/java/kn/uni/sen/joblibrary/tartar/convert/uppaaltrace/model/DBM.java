package kn.uni.sen.joblibrary.tartar.convert.uppaaltrace.model;

import java.util.ArrayList;
import java.util.List;

public class DBM
{
	String id;
	List<ClockBound> boundList = new ArrayList<ClockBound>();

	public DBM(String id)
	{
		this.id = id;
	}

	public String getID()
	{
		return id;
	}

	public void addClockBound(ClockBound bound)
	{
		this.boundList.add(bound);
	}

	public List<ClockBound> getClockBoundList()
	{
		return boundList;
	}
}
