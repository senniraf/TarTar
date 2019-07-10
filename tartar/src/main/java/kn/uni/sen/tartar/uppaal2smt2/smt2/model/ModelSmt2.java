package kn.uni.sen.tartar.uppaal2smt2.smt2.model;

import java.util.ArrayList;
import java.util.List;

public class ModelSmt2
{
	String startComment = "";
	String fileExtra = "";
	String modelName = "";
	StateSmt2 initialState;
	ConstraintSmt2 ctl;

	List<TransitionSmt2> transitionList = new ArrayList<>();
	List<VariableSmt2> variableList = new ArrayList<>();
	List<ClockSmt2> clockList = new ArrayList<>();
	List<ConstraintSmt2> propList = new ArrayList<>();

	public void setModelName(String name)
	{
		modelName = name;
	}

	public String getModelName()
	{
		return modelName;
	}

	public void addStartComment(String comment)
	{
		startComment = comment + startComment;
	}

	public String getStartComment()
	{
		return startComment;
	}

	public void addFileExtra(String extra)
	{
		fileExtra = extra + fileExtra;
	}

	public String getFileExtra()
	{
		return fileExtra;
	}

	public void setInitialState(StateSmt2 init)
	{
		initialState = init;
	}

	public StateSmt2 getInitialState()
	{
		return initialState;
	}

	public void addTransition(TransitionSmt2 trans)
	{
		transitionList.add(trans);
	}

	public TransitionSmt2 getNextTransition(StateSmt2 state)
	{
		for (TransitionSmt2 trans : transitionList)
			if (trans.getFrom() == state)
				return trans;
		return null;
	}

	public List<TransitionSmt2> getTransitionList()
	{
		return transitionList;
	}

	public void addVariable(VariableSmt2 con)
	{
		variableList.add(con);

		if (con instanceof ClockSmt2)
			clockList.add((ClockSmt2) con);
	}

	public List<VariableSmt2> getVariableList()
	{
		return variableList;
	}

	public VariableSmt2 getVariableByName(String name)
	{
		for (VariableSmt2 var : variableList)
			if (var.compareName(name))
				return var;
		return null;
	}

	public VariableSmt2 getDefineByName(String origin)
	{
		for (VariableSmt2 var : variableList)
		{
			if (!!!var.getDefine())
				continue;
			if (var.compareName(origin))
				return var;
		}
		return null;
	}

	public List<VariableSmt2> getAllVariableList()
	{
		List<VariableSmt2> varList = new ArrayList<VariableSmt2>();
		// add global variables
		for (VariableSmt2 var : variableList)
			varList.add(var);

		// add all local variables
		for (TransitionSmt2 trans : transitionList)
		{
			StateSmt2 from = trans.getFrom();
			StateSmt2 to = trans.getTo();

			for (VariableSmt2 var : from.getVariableList())
				if (!varList.contains(var) && (var.getClass() != ClockSmt2.class))
					varList.add(var);

			for (VariableSmt2 var : to.getVariableList())
				if (!varList.contains(var) && (var.getClass() != ClockSmt2.class))
					varList.add(var);
		}
		return varList;
	}

	public void addProperty(ConstraintSmt2 prop)
	{
		propList.add(prop);
	}

	public List<ConstraintSmt2> getPropertyList()
	{
		return propList;
	}

	public List<ClockSmt2> getClockList()
	{
		List<ClockSmt2> clockList = new ArrayList<ClockSmt2>();

		for (ClockSmt2 clock : this.clockList)
			clockList.add(clock);

		for (TransitionSmt2 trans : transitionList)
		{
			StateSmt2 from = trans.getFrom();
			StateSmt2 to = trans.getTo();
			for (VariableSmt2 var : from.getVariableList())
				if (!clockList.contains(var) && (var.getClass() == ClockSmt2.class))
					clockList.add((ClockSmt2) var);

			for (VariableSmt2 var : to.getVariableList())
				if (!clockList.contains(var) && (var.getClass() == ClockSmt2.class))
					clockList.add((ClockSmt2) var);
		}
		return clockList;
	}

	public void addCTLProperty(ConstraintSmt2 ctl)
	{
		this.ctl = ctl;
	}
	
	public ConstraintSmt2 getCTLProperty()
	{
		return ctl;
	}
}
