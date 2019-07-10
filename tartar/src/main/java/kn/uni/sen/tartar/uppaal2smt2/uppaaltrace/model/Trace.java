package kn.uni.sen.tartar.uppaal2smt2.uppaaltrace.model;

import java.util.ArrayList;
import java.util.List;

public class Trace
{
	String modelName;
	Node initial;
	List<Clock> clockList = new ArrayList<>();
	List<Variable> varList = new ArrayList<>();
	List<DBM> dbmList = new ArrayList<>();
	List<Node> nodeList = new ArrayList<>();
	List<Transition> transitionList = new ArrayList<>();
	List<Edge> edgeList = new ArrayList<>();
	List<LocationVector> locationVectorList = new ArrayList<>();
	List<VariableVector> variableVectorList = new ArrayList<>();

	public static final String t0Name = "sys.t(0)";

	public Trace(String modelName)
	{
		this.modelName = modelName;
	}

	public String getModelName()
	{
		return modelName;
	}

	public List<Node> getNodeList()
	{
		return nodeList;
	}

	public List<DBM> getDbmList()
	{
		return dbmList;
	}

	public List<Transition> getTansitionList()
	{
		return transitionList;
	}

	public List<Clock> getClockList()
	{
		return clockList;
	}

	public List<Variable> getVariableList()
	{
		return varList;
	}

	public Node getNodeByName(String name)
	{
		for (Node node : nodeList)
		{
			if (node.getName().compareTo(name) == 0)
				return node;
		}
		System.out.println("Warning: Node " + name + " was not found!");
		return null;
	}

	public Clock getClockByID(String id)
	{
		for (Clock clock : clockList)
		{
			if (clock.getID().compareTo(id) == 0)
				return clock;
		}
		System.out.println("Warning: Clock " + id + " was not found!");
		return null;
	}

	public DBM getDbmByName(String name)
	{
		// there are sometimes empty sign inside of string
		String name2 = name.trim();
		for (DBM dbm : dbmList)
		{
			if (dbm.getID().compareTo(name) == 0)
				return dbm;
			if (dbm.getID().compareTo(name2) == 0)
				return dbm;
		}
		System.out.println("Warning: DBM " + name + " was not found!");
		return null;
	}

	public Transition getTransitionByNode(Node node)
	{
		for (Transition trans : transitionList)
			if (trans.getNodeFrom() == node)
				return trans;
		// System.out.println("Warning: Transition for node " + node.getName() +
		// " was not found.");
		return null;
	}

	public Edge getEdgeByName(String name)
	{
		for (Edge edge : edgeList)
			if (edge.getId().compareTo(name) == 0)
				return edge;
		System.out.println("Warning: Edge " + name + " was not found.");
		return null;
	}

	public LocationVector getLocationVectorByName(String name)
	{
		for (LocationVector loc : locationVectorList)
			if (loc.getId().compareTo(name) == 0)
				return loc;
		System.out.println("Warning: location vector " + name + " was not found.");
		return null;
	}

	public void addNode(Node node)
	{
		nodeList.add(node);
	}

	public void addDBM(DBM dbm)
	{
		dbmList.add(dbm);
	}

	public void addTransition(Transition transition)
	{
		transitionList.add(transition);
	}

	public void addClock(Clock clock)
	{
		clockList.add(clock);
	}

	public void addEdge(Edge edge)
	{
		edgeList.add(edge);
	}

	public void addLocationVector(LocationVector locVec)
	{
		locationVectorList.add(locVec);
	}

	public void addVariableVector(VariableVector vec)
	{
		variableVectorList.add(vec);
	}

	public void setInitialNode(Node initial)
	{
		this.initial = initial;
	}

	public Node getInitialNode()
	{
		return initial;
	}

	public void addVariable(Variable variable)
	{
		varList.add(variable);
	}

	public List<VariableState> getVariableListByName(String variableVector)
	{
		for (VariableVector vec : variableVectorList)
			if (vec.getID().compareTo(variableVector) == 0)
				return vec.getVariableList();
		return null;
	}

	public Variable getVariableByName(String id)
	{
		for (Variable var : varList)
		{
			if (var.name.compareTo(id) == 0)
				return var;
		}
		return null;
	}

	public int getTraceLength()
	{
		return transitionList.size();
	}
}
