package kn.uni.sen.tartar.uppaal2smt2.uppaaltrace.model;

import java.util.ArrayList;
import java.util.List;

public class Transition
{
	Node nodeFrom;
	Node nodeTo;
	List<Edge> edgeList = new ArrayList<Edge>();

	public Transition(Node from, Node to, String edgeList, Trace trace)
	{
		this.nodeFrom = from;
		this.nodeTo = to;
		ConvertParseEdgeList(edgeList, trace);
	}

	public Node getNodeTo()
	{
		return nodeTo;
	}

	public Node getNodeFrom()
	{
		return nodeFrom;
	}

	public List<Edge> getEdgeList()
	{
		return edgeList;
	}

	void ConvertParseEdgeList(String edgeListText, Trace trace)
	{
		String[] splitList = edgeListText.split(" ");
		for (String edge : splitList)
			this.edgeList.add(trace.getEdgeByName(edge));
	}

	public boolean isClockReset(Clock clock)
	{
		String update = "" + clock.getName() + " := 0";
		for (Edge edge : edgeList)
		{
			if (edge.getUpdate().compareTo(update) == 0)
				return true;
		}
		return false;
	}

	public boolean isClockReset(String name)
	{
		String update = "" + name + ":=0";
		for (Edge edge : edgeList)
		{
			String t = edge.getUpdate().replace(" ", "");
			if (t.compareTo(update) == 0)
				return true;
			String templ = edge.getProcessName();
			if (!!!name.startsWith(templ))
				continue;
			String name2 = name.substring(templ.length() + 1) + ":=0";
			if (t.contains(name2))
				return true;
		}
		return false;
	}
}
