package kn.uni.sen.joblibrary.tartar.convert.uppaaltrace.model;

public class Edge
{
	String id;
	String guard = "";
	String sync = "";
	String update = "";
	String from = "";
	String to = "";

	public Edge(String id, String from, String to)
	{
		this.id = id;
		this.from = from;
		this.to = to;
	}

	public String getProcessName()
	{
		int index = id.indexOf(".");
		if (index == -1)
			return "";

		return id.substring(0, index);
	}

	public String getId()
	{
		return id;
	}

	public String getFrom()
	{
		return from;
	}

	public String getTo()
	{
		return to;
	}

	public void setGuard(String guard)
	{
		this.guard = guard;
	}

	public String getGuard()
	{
		return guard;
	}

	public void setSync(String sync)
	{
		this.sync = sync;
	}

	public String getSync()
	{
		return sync;
	}
	
	public void setUpdate(String update)
	{
		this.update = update;
	}

	public String getUpdate()
	{
		return update;
	}
}
