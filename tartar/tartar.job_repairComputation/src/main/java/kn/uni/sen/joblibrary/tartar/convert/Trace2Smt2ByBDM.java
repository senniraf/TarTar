package kn.uni.sen.joblibrary.tartar.convert;

import java.util.List;

import kn.uni.sen.joblibrary.tartar.convert.smt2.model.ClockSmt2;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.ConstantSmt2;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.ConstraintSmt2;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.ModelSmt2;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.StateSmt2;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.TextSmt2;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.TransitionSmt2;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.VariableSmt2;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.ConstraintSmt2.Design;
import kn.uni.sen.joblibrary.tartar.convert.uppaalmodel.model.Model;
import kn.uni.sen.joblibrary.tartar.convert.uppaaltrace.model.Clock;
import kn.uni.sen.joblibrary.tartar.convert.uppaaltrace.model.ClockBound;
import kn.uni.sen.joblibrary.tartar.convert.uppaaltrace.model.DBM;
import kn.uni.sen.joblibrary.tartar.convert.uppaaltrace.model.Edge;
import kn.uni.sen.joblibrary.tartar.convert.uppaaltrace.model.Node;
import kn.uni.sen.joblibrary.tartar.convert.uppaaltrace.model.Trace;
import kn.uni.sen.joblibrary.tartar.convert.uppaaltrace.model.Transition;
import kn.uni.sen.joblibrary.tartar.convert.uppaaltrace.model.VariableState;
import kn.uni.sen.jobscheduler.common.model.JobContext;

/**
 * 1. version of uppaal2smt2 by rewriting the DBMs
 * 
 * @author Martin Koelbl
 */
public class Trace2Smt2ByBDM extends Transformer
{
	// ignore variable changes, since we are only interested in clocks
	boolean bOnlyClocks = true;

	Trace trace;

	int commentDepth;
	ModelSmt2 smt2;

	// helper variables
	Integer zoneCounter = 0;
	StateSmt2 currentState = null;

	public Trace2Smt2ByBDM(JobContext jobContext)
	{
		super(jobContext);
		variant = "; by BDM\n";
		fileExtra = "_bdm";
	}

	void createClockList(StateSmt2 stateSmt2, List<Clock> clockList, Transition trans, int zoneCounter)
	{
		if (zoneCounter == 1)
		{
			for (Clock clock : clockList)
			{
				ClockSmt2 clockSmt2 = new ClockSmt2(clock.getID(), zoneCounter);
				stateSmt2.addVariable(clockSmt2);
			}
			return;
		}

		for (Clock clock : clockList)
		{
			ClockSmt2 clockSmt2 = new ClockSmt2(clock.getID(), zoneCounter);
			clockSmt2.addValue("" + t0Name + zoneCounter);
			stateSmt2.addVariable(clockSmt2);
		}
	}

	TextSmt2 parseConstraint(String value, int zoneCounter, StateSmt2 state)
	{
		if (value.compareTo(Trace.t0Name) == 0)
			value = t0Name;

		value = value.replace("sys.", "");

		VariableSmt2 clock = smt2.getVariableByName(value + zoneCounter);
		if (clock != null)
			return clock;

		String op = "<=";
		VariableSmt2 var1 = null;
		VariableSmt2 var2 = null;
		ConstraintSmt2 con = new ConstraintSmt2(op, var1, var2);
		return con;
	}

	void convertNodeBound(StateSmt2 stateSmt2, int zoneCounter, ClockBound bound)
	{
		// ignore infinite boundaries
		if (bound.getBound().compareTo("inf") == 0)
			return;

		// <= x1 - x2 0
		String firstName = bound.getFirst().getID();
		String secondName = bound.getSecond().getID();

		VariableSmt2 var1 = smt2.getVariableByName(firstName);
		VariableSmt2 var2 = smt2.getVariableByName(secondName);

		ConstraintSmt2 con = null;
		if (var1 == var2)
			return;
		else if (firstName.compareTo(Trace.t0Name) == 0)
		{
			// first clock is missing
			ConstantSmt2 constant = new ConstantSmt2(bound.getBoundNegated());
			con = new ConstraintSmt2(bound.getCompareNegated(), var2, constant);
		} else if (secondName.compareTo(Trace.t0Name) == 0)
		{
			// second clock is missing
			ConstantSmt2 constant = new ConstantSmt2(bound.getBound());
			con = new ConstraintSmt2(bound.getCompare(), var2, constant);
		} else
		{
			// both clocks are set
			ConstantSmt2 constant = new ConstantSmt2(bound.getBound());
			ConstraintSmt2 con_i = new ConstraintSmt2("-", var1, var2);
			con = new ConstraintSmt2(bound.getCompare(), con_i, constant);
		}
		if (con != null)
			stateSmt2.addConstraint(con);
	}

	StateSmt2 convertState(Node node, Transition trans, int zoneCounter)
	{
		StateSmt2 stateSmt2 = new StateSmt2(zoneCounter);
		createClockList(stateSmt2, trace.getClockList(), trans, zoneCounter);
		DBM dbm = node.getDBM();
		List<ClockBound> boundList = dbm.getClockBoundList();
		for (ClockBound bound : boundList)
		{
			convertNodeBound(stateSmt2, zoneCounter, bound);
		}
		return stateSmt2;
	}

	TransitionSmt2 convertTransition(Trace trace2, Transition trans, StateSmt2 stateFrom, StateSmt2 stateTo,
			int zoneCounter)
	{
		// todo: find guards
		TransitionSmt2 transitionSmt2 = new TransitionSmt2("", stateFrom, stateTo);
		smt2.addTransition(transitionSmt2);

		for (ClockSmt2 clock : stateFrom.getClockList())
		{
			if (clock.getOrigin().compareTo(Transformer.t0Name) == 0)
				continue;

			ClockSmt2 clockTo = transitionSmt2.getClock(clock.getOrigin(), clock.getIndex() + 1);
			TextSmt2 dif = null;
			if ((trans != null) && trans.isClockReset(clock.getOrigin()))
			{
				clockTo.setLastSetStep(zoneCounter);
				transitionSmt2.addReset(clock);
				dif = new ConstantSmt2("0");
			} else
			{
				ClockSmt2 clockDif = transitionSmt2.getClock(Transformer.t0Name, clock.getIndex());
				clockTo.setLastSetStep(clock.getLastSetStep());
				dif = new ConstraintSmt2("+", clock, clockDif);
			}
			ConstraintSmt2 reset = new ConstraintSmt2("=", clockTo, dif);
			reset.setDesign(Design.DELAY);
			transitionSmt2.addConstraint(reset);
		}

		List<Edge> edgeList = trans.getEdgeList();
		for (Edge edge : edgeList)
		{
			transitionSmt2.addFromName(edge.getFrom());
			transitionSmt2.addToName(edge.getTo());
		}

		return transitionSmt2;
	}

	public String followTrace(Trace trace)
	{
		String text = "";
		Node node = trace.getInitialNode();
		zoneCounter = 1;
		Transition trans = trace.getTransitionByNode(node);
		currentState = convertState(node, trans, zoneCounter);
		smt2.setInitialState(currentState);
		createVariables(trace.getVariableListByName(node.getVariableVector()));
		for (zoneCounter = 2; trans != null; zoneCounter++)
		{
			Node node2 = trans.getNodeTo();
			if (node == node2)
			{
				System.out.println("Warning: Self loop detected");
				break;
			}
			node = node2;

			StateSmt2 stateSmtFrom = currentState;
			currentState = convertState(node, trans, zoneCounter);

			convertTransition(trace, trans, stateSmtFrom, currentState, zoneCounter);

			// get next transition
			trans = trace.getTransitionByNode(node);
		}
		return text;
	}

	protected void createVariables(List<VariableState> variableListByName)
	{
	}

	void createInitial(Trace trace)
	{
	}

	public ModelSmt2 transform(Trace trace, Model model)
	{
		smt2 = new ModelSmt2();
		if (trace == null)
		{
			System.out.println("Error: Trace was not loaded.");
			return null;
		}
		if (trace.getInitialNode() == null)
			createInitial(trace);
		if (trace.getInitialNode() == null)
		{
			// model.get
			System.out.println("Error: Initial node is missing.");
			return null;
		}

		this.trace = trace;

		smt2.setModelName(trace.getModelName());
		followTrace(trace);

		return smt2;
	}
}
