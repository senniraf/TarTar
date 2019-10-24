package kn.uni.sen.joblibrary.tartar.convert.uppaalmodel.model;

import java.util.ArrayList;
import java.util.List;

public class Location
{
	// id in uppaal file
	String id;
	// counter id of transition and states
	int modelID = 0;
	List<String> nameList = new ArrayList<String>();
	boolean urgent;
	List<ConstraintModel> invariantList = new ArrayList<>();

	public Location(String id)
	{
		this.id = id;
	}

	public void addName(String name)
	{
		nameList.add(name);
	}

	public List<String> getNameList()
	{
		return nameList;
	}

	public String getID()
	{
		return id;
	}

	public void setUrgent(boolean urgent)
	{
		this.urgent = urgent;
	}

	public boolean isUrgent()
	{
		return this.urgent;
	}

	public void addLabel(String kind, String value)
	{
		if (value == null)
			return;
		if (kind.compareTo("invariant") == 0)
		{
			ConstraintModel inv = new ConstraintModel(modelID, value);
			invariantList.add(inv);
		}
	}

	public List<ConstraintModel> getInvariantList()
	{
		// System.out.println(invariantList);
		return invariantList;
	}

	public static String[] splitInvariant(String inv)
	{
		inv = inv.replaceAll(" ", "");
		// "x<=1" -> ["x", "<=", "1"]
		int indexLow = inv.length();
		int indexHeight = -1;
		int index = inv.indexOf("<");
		if ((index >= 0) && (index < indexLow))
			indexLow = index;
		if (index > indexHeight)
			indexHeight = index;
		index = inv.indexOf(">");
		if ((index >= 0) && (index < indexLow))
			indexLow = index;
		if (index > indexHeight)
			indexHeight = index;
		index = inv.indexOf("=");
		if ((index >= 0) && (index < indexLow))
			indexLow = index;
		if (index > indexHeight)
			indexHeight = index;
		String[] ret = {};
		if ((indexLow == -1) || (indexHeight == -1))
			return ret;
		String val1 = inv.substring(0, indexLow);
		String val2 = inv.substring(indexLow, indexHeight + 1);
		String val3 = inv.substring(indexHeight + 1);
		String[] ret2 = { val1, val2, val3 };
		return ret2;
	}

	public void setIDModel(int id)
	{
		modelID = id;
	}

	public int getIDModel()
	{
		return modelID;
	}

	public boolean isErrorState()
	{
		for (String name : nameList)
			if (name.toLowerCase().startsWith("error"))
				return true;
		return false;
	}
}
