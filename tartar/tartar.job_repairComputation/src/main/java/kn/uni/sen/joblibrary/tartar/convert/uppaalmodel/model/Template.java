package kn.uni.sen.joblibrary.tartar.convert.uppaalmodel.model;

import java.util.LinkedList;
import java.util.List;

import kn.uni.sen.joblibrary.tartar.convert.HelperText;
import kn.uni.sen.joblibrary.tartar.convert.uppaaltrace.model.Edge;

public class Template
{
	Model model;
	List<Location> locationList = new LinkedList<Location>();
	List<ModelTransition> transitionList = new LinkedList<ModelTransition>();
	Location init;
	String name = "";
	String declaration = "";
	String paraList = "";
	boolean hasErrorState;

	public Template(Model model)
	{
		this.model = model;
	}

	public void addName(String name)
	{
		this.name = name;
	}

	public Model getModel()
	{
		return model;
	}

	public void addDeclaration(String declaration)
	{
		this.declaration = declaration;
		parseDeclaration(declaration);
	}

	public String[] getDeclarationList()
	{
		return declaration.split(";\n");
	}

	public String getVariableValue(String name)
	{
		String[] list = getDeclarationList();
		for (String str : list)
		{
			String[] list2 = str.split(" ");
			if (list2.length <= 3)
				continue;

			if (list2[1].contains(name))
				return list2[3];
		}
		return null;
	}

	public String getName()
	{
		return name;
	}

	public void addLocation(Location loc)
	{
		hasErrorState |= loc.isErrorState();
		locationList.add(loc);
	}

	public List<Location> getLocationList()
	{
		return locationList;
	}

	public Location getLocationByName(String name)
	{
		int index = name.indexOf(".");
		// String templName = "";
		String locName = name;
		if ((index != -1) && (index != 0))
		{
			// templName = name.substring(0, index);
			locName = name.substring(index + 1);
		}
		// if (templName.compareTo(this.name) != 0)
		// return null;

		List<Location> locationList = getLocationList();
		for (Location loc : locationList)
			for (String str : loc.getNameList())
				if (str.compareTo(locName) == 0)
					return loc;

		Location l = getLocationByID(locName);
		if (l != null)
			return l;
		System.out.println("Warning: Location " + name + " was not found!");
		return null;
	}

	public Location getLocationByID(String id)
	{
		for (Location loc : locationList)
			if (loc.getID().compareTo(id) == 0)
				return loc;
		if (id.startsWith("_"))
		{
			// if state has no name, then the trace file uses the "_"+id
			id = id.substring(1);
			for (Location loc : locationList)
				if (loc.getID().compareTo(id) == 0)
					return loc;
		}
		return null;
	}

	public void setParameterList(String paraList)
	{
		this.paraList = paraList;
	}

	public String getParameterList()
	{
		return paraList;
	}

	public void setInit(String name)
	{
		if (name == null)
			return;
		Location loc = getLocationByID(name);
		// todo:
		if (loc != null)
			init = loc;
	}

	public Location getInit()
	{
		return init;
	}

	public void addTransition(ModelTransition trans)
	{
		transitionList.add(trans);
	}

	public List<ModelTransition> getTransitionList()
	{
		return transitionList;
	}

	public VariableModel parseVariable(String name)
	{
		VariableModel var = VariableModel.parseVariable(name, paraList);
		if (var != null)
			return var;

		return VariableModel.parseVariable(name, declaration);
	}

	private Location getLocation(String name)
	{
		if (name.startsWith("_id"))
			name = name.replaceFirst("_id", "id");
		for (Location loc : locationList)
		{
			if (loc.getID().compareTo(name) == 0)
				return loc;
			for (String n : loc.getNameList())
				if (n.compareTo(name) == 0)
					return loc;
		}
		return null;
	}

	private String removeTemplate(String name)
	{
		int index = name.indexOf(".");
		if (index < 0)
			return name;
		return name.substring(index + 1);
	}

	public ModelTransition getTransition(Edge edge)
	{
		Location locS = getLocation(removeTemplate(edge.getFrom()));
		Location locE = getLocation(removeTemplate(edge.getTo()));
		for (ModelTransition trans : transitionList)
		{
			Location ls = getLocation(trans.from);
			if (locS != ls)
				continue;
			Location le = getLocation(trans.to);
			if (locE != le)
				continue;
			String syncEdge = edge.getSync();
			ConstraintModel sync = trans.getSynchronisation();
			if ((syncEdge.compareTo("tau") == 0) && (sync == null))
				return trans;
			if ((syncEdge.compareTo("tau") == 0) || (sync == null))
				continue;
			syncEdge = syncEdge.replace("?", "").replace("!", "");
			String syncModel = sync.getLabel().replace("?", "").replace("!", "");
			syncModel = syncModel.replace(" ", "");
			if (syncEdge.compareTo(syncModel) != 0)
				continue;
			return trans;
		}
		return null;
	}

	public boolean hasErrorState()
	{
		return hasErrorState;
	}

	public void parseDeclaration(String decl)
	{
		decl = HelperText.deleteComment(decl);
	}
}
