package kn.uni.sen.joblibrary.tartar.convert.uppaaltrace.model;

public class LocationVector
{
	String id;
	String locations;

	public LocationVector(String id, String loc)
	{
		this.id = id;
		this.locations = loc;
	}

	public String getId()
	{
		return id;
	}

	public String[] getLocationList()
	{
		String[] list = locations.split(" ");
		return list;
	}
}
