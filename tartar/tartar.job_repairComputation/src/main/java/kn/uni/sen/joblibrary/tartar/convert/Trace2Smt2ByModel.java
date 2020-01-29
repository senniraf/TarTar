package kn.uni.sen.joblibrary.tartar.convert;

import java.util.ArrayList;
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
import kn.uni.sen.joblibrary.tartar.convert.uppaalmodel.model.ConstantModel;
import kn.uni.sen.joblibrary.tartar.convert.uppaalmodel.model.ConstraintInterface;
import kn.uni.sen.joblibrary.tartar.convert.uppaalmodel.model.ConstraintModel;
import kn.uni.sen.joblibrary.tartar.convert.uppaalmodel.model.Location;
import kn.uni.sen.joblibrary.tartar.convert.uppaalmodel.model.Model;
import kn.uni.sen.joblibrary.tartar.convert.uppaalmodel.model.ModelTransition;
import kn.uni.sen.joblibrary.tartar.convert.uppaalmodel.model.Template;
import kn.uni.sen.joblibrary.tartar.convert.uppaalmodel.model.TemplateModel;
import kn.uni.sen.joblibrary.tartar.convert.uppaalmodel.model.VariableModel;
import kn.uni.sen.joblibrary.tartar.convert.uppaaltrace.model.Edge;
import kn.uni.sen.joblibrary.tartar.convert.uppaaltrace.model.LocationVector;
import kn.uni.sen.joblibrary.tartar.convert.uppaaltrace.model.Node;
import kn.uni.sen.joblibrary.tartar.convert.uppaaltrace.model.Process;
import kn.uni.sen.joblibrary.tartar.convert.uppaaltrace.model.Trace;
import kn.uni.sen.joblibrary.tartar.convert.uppaaltrace.model.Transition;
import kn.uni.sen.joblibrary.tartar.convert.uppaaltrace.model.VariableState;
import kn.uni.sen.jobscheduler.common.model.RunContext;

public class Trace2Smt2ByModel extends Trace2Smt2ByBDM
{
	Model model;
	List<VariableSmt2> varList = new ArrayList<>();

	public Trace2Smt2ByModel(RunContext jobContext)
	{
		super(jobContext);
		variant = "; by extra model\n";
		fileExtra = "_inv";
	}

	public VariableSmt2 getVariable(String name, StateSmt2 state, TemplateModel templ, int count)
	{
		String processName = "";
		if ((templ != null) && (templ.getName().compareTo("") != 0))
			processName = templ.getName() + ".";

		// check state and global variables already created
		String varName = name + count;
		VariableSmt2 var = state.getVariableByName(varName);
		if (var == null)
			var = state.getVariableByName(processName + name);
		if (var == null)
			var = smt2.getVariableByName(name);
		if (var != null)
			return var;

		// check for local value of variable
		String value = null;
		if (templ != null)
			value = templ.getTemplate().getVariableValue(name);
		if (value != null)
		{
			var = new VariableSmt2(processName + varName, "Int", value, count, null);
			state.addVariable(var);
			return var;
		}

		// check for global value of variable
		VariableSmt2 value2 = createVariableByName(templ, name, count);
		return value2;
	}

	public void convertInvariantText(StateSmt2 state, Location loc, ConstraintModel inv, TemplateModel templ, int count)
	{
		// todo: perhaps old
		ConstraintInterface conNew = inv.parseConstraint(templ);
		if (conNew == null)
		{
			System.out.println("Warning: Is every invariant correctly parsed?");
			return;
		}
		conNew = filterConstraint(conNew);
		if (conNew == null)
			return;
		// System.out.println(ConstraintModel.getConstraintText(conNew));

		for (boolean incClock : new Boolean[] { Boolean.FALSE, Boolean.TRUE })
		{
			TextSmt2 text = convertConstraint2SMT2(conNew, state, templ, zoneCounter, incClock, inv.getID(),
					loc.getIDModel());
			if (text == null)
			{
				System.out.println("Warning: Invariant constraint not coverted to SMT2");
				return;
			}
			ConstraintSmt2 con = (ConstraintSmt2) text;
			con.setID(loc.getIDModel());
			con.setIDModel(loc.getIDModel());
			con.setDesign(ConstraintSmt2.Design.INVARIANT);
			state.addConstraint(con);
		}
	}

	public String containsFirstOfList(String val, String[] list)
	{
		String first = null;
		int min = val.length();
		for (String opi : list)
		{
			int index = val.indexOf(opi);
			if ((index != -1) && (index < min))
			{
				min = index;
				first = opi;
			}
		}
		return first;
	}

	public VariableSmt2 createVariableByName(TemplateModel templ, String name, int step)
	{
		VariableModel varM = null;
		if (templ != null)
		{
			varM = templ.getTemplate().parseVariable(name);
			if ((varM != null) && !!!name.contains("."))
				name = templ.getName() + "." + name;
		}
		if (varM == null)
			varM = model.parseGlobalVariable(name);
		if (varM == null)
			return null;

		VariableSmt2 var = null;
		if (varM.isType("Clock"))
		{
			var = new ClockSmt2(name, step);
		} else
		{
			if (varM.isConstant())
				step = 0;
			var = new VariableSmt2(name, varM.getType(), varM.getValue(), step, null);
			if (varM.isConstant())
			{
				var.setDefine(true);
			}
		}
		return var;
	}

	public VariableSmt2 getVariableByName(String origin, String process, StateSmt2 state, int count)
	{
		if (origin.isEmpty())
			return null;
		if (state == null)
			return null;
		// todo: -1 or some labelID???
		String name = VariableSmt2.getName(origin, count, null);
		String orgName = (process != null) && (process.compareTo("") != 0) ? process + "." + origin : origin;
		String locName = (process != null) && (process.compareTo("") != 0) ? process + "." + name : name;
		VariableSmt2 var = state.getVariableByName(locName);
		if (var != null)
			return var;
		var = state.getVariableByName(name);
		if (var != null)
			return var;

		var = smt2.getVariableByName(locName);
		if (var != null)
			return var;

		var = smt2.getDefineByName(origin);
		if (var != null)
			return var;

		var = createNextIndexVariable(orgName, state);
		if (var != null)
			return var;

		TemplateModel templ = model.getTemplateByName(process);
		var = createVariableByName(templ, origin, count);
		if (var != null)
		{
			String nameVar = var.getName();
			// System.out.println("new " + nameVar + " " + var.getIndex());
			if (nameVar.contains("."))
				state.addVariable(var);
			else
				smt2.addVariable(var);
			varList.add(var);
		}
		return var;
	}

	String deleteComments(String text)
	{
		if (!!!text.contains("//"))
			return text;
		String[] line = text.split("\n");
		String ret = "";
		for (String s : line)
		{
			int index = s.indexOf("//");
			if (index >= 0)
				s = s.substring(0, index);
			ret += s;
		}
		return ret;
	}

	public TextSmt2 convertConstraint2SMT2(ConstraintInterface con, StateSmt2 state, TemplateModel templ,
			int zoneCounter, boolean withDelay, int id, int idModel)
	{
		// List<TextSmt2> list = new ArrayList<>();
		if (con.getClass() == ConstraintModel.class)
		{
			ConstraintModel cm = (ConstraintModel) con;
			ConstraintSmt2 con2 = new ConstraintSmt2(cm.getOperator().replace("==", "="));
			for (ConstraintInterface ci : cm.getConstraintList())
			{
				TextSmt2 child = convertConstraint2SMT2(ci, state, templ, zoneCounter, withDelay, id, idModel);
				con2.addCon(child);
				con2.setID(id);
				con2.setIDModel(idModel);
			}
			return con2;
		}
		if (con.getClass() == VariableModel.class)
		{
			VariableModel vm = (VariableModel) con;
			String tName = null;
			if (templ != null)
				tName = templ.getName();
			else
				tName = vm.getTemplateName();
			VariableSmt2 var = getVariableByName(vm.getName(), tName, state, zoneCounter);
			if (var == null)
			{
				System.out.println("Error: missing variable!");
				return null;
			}

			if (withDelay && (var.getType().compareTo("clock") == 0))
			{
				TextSmt2 delay = getVariableByName(Transformer.t0Name, tName, state, zoneCounter);
				if (delay == null)
				{
					System.out.println("Warning: Missing delay");
					return var;
				}

				ConstraintSmt2 con2 = new ConstraintSmt2("+");
				con2.setID(id);
				con2.setIDModel(idModel);
				con2.addCon(var);
				con2.addCon(delay);
				return con2;
			}
			return var;
		}
		if (con.getClass() == ConstantModel.class)
		{
			ConstantModel vm = (ConstantModel) con;
			return new ConstantSmt2(vm.getValue());
		}
		return null;
	}

	public void convertGuardText(TransitionSmt2 trans, ModelTransition transM, TemplateModel templ, StateSmt2 stateFrom,
			int count)
	{
		ConstraintModel guardModel = transM.getGuard();
		if (guardModel == null)
			return;
		ConstraintInterface guard = guardModel.parseConstraint(templ);
		if (guard == null)
			return;
		// String text = ConstraintModel.getConstraintText(guard);
		// System.out.println(text);
		guard = filterConstraint(guard);
		// if (guard.compareTo("1") == 0)
		if (guard == null)
			return;

		TextSmt2 conver = convertConstraint2SMT2(guard, stateFrom, templ, zoneCounter - 1, true, guardModel.getID(),
				transM.getIDModel());
		if (conver == null)
		{
			System.out.println("Warning: Some guard was not parsed " + guard);
			return;
		}
		ConstraintSmt2 con = (ConstraintSmt2) conver;
		con.setDesign(Design.GUARD);
		trans.addConstraint(con);
	}

	private boolean hasClock(ConstraintInterface inter)
	{
		if (inter instanceof ConstraintModel)
		{
			ConstraintModel cm = (ConstraintModel) inter;
			for (ConstraintInterface child : cm.getConstraintList())
				if (hasClock(child))
					return true;
		} else if (inter instanceof VariableModel)
		{
			VariableModel var = (VariableModel) inter;
			if (var.getType().compareTo("Clock") == 0)
				return true;
		}
		return false;
	}

	private ConstraintInterface filterConstraint(ConstraintInterface guard)
	{
		if (!!!bOnlyClocks)
			return guard;
		// todo: filter if some conditions are no constraints.
		if (guard instanceof ConstraintModel)
		{
			ConstraintModel cm = (ConstraintModel) guard;
			if ((cm.getOperator().compareTo("&&") == 0) || (cm.getOperator().compareTo("||") == 0))
			{
				List<ConstraintInterface> interList = new ArrayList<>();
				for (ConstraintInterface child : cm.getConstraintList())
					if (hasClock(child))
						interList.add(child);
				if (interList.size() == cm.getConstraintList().size())
					return cm;
				if (interList.size() == 1)
					return interList.get(0);
				if (interList.size() == 0)
					return null;
			} else
			{
				for (ConstraintInterface child : cm.getConstraintList())
					if (hasClock(child))
						return cm;
			}
		}
		if (!!!hasClock(guard))
			return null;

		return guard;
	}

	private void convertUpdateText(TransitionSmt2 transitionSmt2, ModelTransition mt, Edge edge, StateSmt2 stateFrom,
			StateSmt2 stateTo)
	{
		String update = edge.getUpdate();
		if (update.compareTo("1") == 0)
			return;

		String[] lines = update.split(",");
		for (String line : lines)
		{
			line = line.replace(" ", "");
			int index = line.indexOf(":=");
			if (index != -1)
			{
				String s1 = line.substring(0, index);
				String s2 = line.substring(index + 2);
				// VariableSmt2 v1 = stateFrom.getVariableByOrigin(s1);
				VariableSmt2 v1To = stateTo.getVariableByOrigin(s1);
				if (v1To == null)
					v1To = stateTo.getVariableByOrigin(edge.getProcessName() + "." + s1);
				// if (v1To instanceof ClockSmt2)
				// reset
				// continue;
				if (v1To == null)
					v1To = createNextIndexVariable(s1, stateTo);
				if (v1To == null)
				{
					System.out.println("Warning: unkown variable " + s1);
					continue;
				}
				boolean delay = v1To instanceof ClockSmt2;
				if (bOnlyClocks && !delay)
					return;
				TextSmt2 v2 = parseUpdateValue(s2, stateFrom);
				ConstraintSmt2 con = new ConstraintSmt2("=", v1To, v2);
				if (delay)
				{
					con.setDesign(Design.DELAY);
					transitionSmt2.addReset((ClockSmt2) v1To);
				} else
					con.setDesign(Design.UPDATE);
				if (mt != null)
					con.setIDModel(mt.getIDModel());
				transitionSmt2.addConstraint(con);
				continue;
			}
			System.out.println("Warning: Some update was not parsed " + update);
		}
	}

	private TextSmt2 parseUpdateValue(String update, StateSmt2 stateFrom)
	{
		if ((update == null) || (update.isEmpty()))
			return null;

		TextSmt2 ret = stateFrom.getVariableByOrigin(update);
		if (ret != null)
			return ret;

		if (update.startsWith("!"))
		{
			TextSmt2 v1 = parseUpdateValue(update.substring(1), stateFrom);
			ret = new ConstraintSmt2("!", v1);
			return ret;
		}

		String[] opList = new String[] { "\\+", "-", "/", "\\*" };
		for (String op : opList)
		{
			String[] split = update.split(op);
			if (split.length <= 1)
				continue;
			TextSmt2 v1 = parseUpdateValue(split[0], stateFrom);
			TextSmt2 v2 = parseUpdateValue(split[1], stateFrom);
			ret = new ConstraintSmt2(op.replace("\\", ""), v1, v2);
			return ret;
		}
		if (ret == null)
			ret = new ConstantSmt2(update);
		return ret;
	}

	private VariableSmt2 createNextIndexVariable(String s1, StateSmt2 state)
	{
		if (s1.isEmpty())
			return null;
		VariableSmt2 last = null;
		for (VariableSmt2 var : varList)
			if (var.getOrigin().compareTo(s1) == 0)
			{
				last = var;
				break;
			}
		if (last == null)
		{
			return null;
		}
		if ((last.getIndex() == 0) || (last.getIndex() == state.getIndex()))
			return last;

		VariableSmt2 next = new VariableSmt2(last.getOrigin(), last.getType(), null, state.getIndex(), null);
		varList.remove(last);
		varList.add(next);
		state.addVariable(next);
		return next;
	}

	StateSmt2 convertState(Node node, Transition trans, int zoneCounter)
	{
		StateSmt2 stateSmt2 = new StateSmt2(zoneCounter);
		createClockList(stateSmt2, trace.getClockList(), trans, zoneCounter);

		LocationVector locVec = trace.getLocationVectorByName(node.getLocationVector());
		stateSmt2.setLocationList(locVec.getLocationList());

		// List<VariableState> varList =
		// trace.getVariableListByName(node.getVariableVector());
		/*
		 * System.out.println(node.getName()); if (varList != null) for
		 * (VariableState var : varList) { System.out.println(var.getID() + " "
		 * + var.getValue()); } System.out.println("");
		 */

		for (String locName : locVec.getLocationList())
		{
			TemplateModel templ = model.getTemplateByLocationName(locName);
			if (templ == null)
				continue;
			Location loc = templ.getTemplate().getLocationByName(locName);
			if (loc == null)
				continue;
			if (loc.isUrgent())
				stateSmt2.setUrgent(true);
			for (ConstraintModel inv : loc.getInvariantList())
				convertInvariantText(stateSmt2, loc, inv, templ, zoneCounter);
			stateSmt2.addUppaalID(loc.getID());
			stateSmt2.addFileID(loc.getIDModel());
		}
		if (stateSmt2.isUrgent())
		{
			ClockSmt2 difClock = null;
			for (ClockSmt2 clock : stateSmt2.getClockList())
				if (clock.getOrigin().compareTo(Transformer.t0Name) == 0)
					difClock = clock;
			if (difClock != null)
			{
				ConstantSmt2 const0 = new ConstantSmt2("0");
				ConstraintSmt2 urgent = new ConstraintSmt2("=", difClock, const0);
				urgent.setDesign(Design.URGENT);
				stateSmt2.addConstraint(urgent);
			}
		}
		return stateSmt2;
	}

	boolean compareValues(String s1, String s2)
	{
		return s1.replace(" ", "").compareTo(s2.replace(" ", "")) == 0;
	}

	ModelTransition getTransition(Edge edge)
	{
		String processName = edge.getProcessName();
		TemplateModel process = model.getTemplateByName(processName);
		List<ModelTransition> list = process.getTemplate().getTransitionList();

		String sync = edge.getSync();
		String action = edge.getUpdate();

		for (ModelTransition t : list)
		{
			Location locationFrom = process.getTemplate().getLocationByID(t.getFrom());
			List<String> listname = locationFrom.getNameList();
			String locationNameFrom = processName + (listname.size() > 0 ? "." + listname.get(0) : "");

			Location locationTo = process.getTemplate().getLocationByID(t.getTo());
			listname = locationTo.getNameList();
			String locationNameTo = processName + (listname.size() > 0 ? "." + listname.get(0) : "");

			if (locationNameFrom.compareTo(edge.getFrom()) != 0)
				continue;
			if (locationNameTo.compareTo(edge.getTo()) != 0)
				continue;

			ConstraintModel con = t.getGuard();
			String conText = "1";
			if (con != null)
				conText = con.getLabel();
			if (!!!compareValues(conText, edge.getGuard()))
			{
				// System.out.println(conText);
				// System.out.println(edge.getGuard());
				continue;
			}

			con = t.getSynchronisation();
			conText = "tau";
			if (con != null)
				conText = con.getLabel();
			if (!!!compareValues(conText, sync))
			{
				// System.out.println(conText);
				// System.out.println(sync);
				continue;
			}

			con = t.getAssignment();
			conText = "1";
			if (con != null)
				conText = con.getLabel();
			if (!!!compareValues(conText, action))
			{
				// System.out.println(conText);
				// System.out.println(action);
				continue;
			}
			return t;
		}
		return null;
	}

	TransitionSmt2 convertTransition(Trace trace2, Transition trans, StateSmt2 stateFrom, StateSmt2 stateTo,
			int zoneCounter)
	{
		// TransitionSmt2 transitionSmt2 = super.convertTransition(trace2,
		// trans, stateFrom, stateTo, zoneCounter);
		TransitionSmt2 transitionSmt2 = new TransitionSmt2("", stateFrom, stateTo);
		smt2.addTransition(transitionSmt2);

		List<Edge> edgeList = trans.getEdgeList();
		int idFirst = 0;
		for (Edge edge : edgeList)
		{
			TemplateModel templ = model.getTemplateByName(edge.getProcessName());
			if (templ == null)
			{
				System.out.println("Warning: Missing template " + edge.getProcessName());
				continue;
			}
			ModelTransition mt = templ.getTemplate().getTransition(edge);
			if (idFirst == 0)
				idFirst = mt.getIDModel();

			convertGuardText(transitionSmt2, mt, templ, stateFrom, zoneCounter);
			convertUpdateText(transitionSmt2, mt, edge, stateFrom, stateTo);
		}

		// create delay if reset is missin
		for (ClockSmt2 clock : stateFrom.getClockList())
		{
			if (clock.getOrigin().compareTo(Transformer.t0Name) == 0)
				continue;
			ClockSmt2 clockTo = transitionSmt2.getClock(clock.getOrigin(), clock.getIndex() + 1);
			if ((trans != null) && trans.isClockReset(clock.getOrigin()))
			{
				clockTo.setLastSetStep(zoneCounter);
				continue;
			}
			ClockSmt2 clockDif = transitionSmt2.getClock(Transformer.t0Name, clock.getIndex());
			clockTo.setLastSetStep(clock.getLastSetStep());
			ConstraintSmt2 dif = new ConstraintSmt2("+", clock, clockDif);
			ConstraintSmt2 delay = new ConstraintSmt2("=", clockTo, dif);
			delay.setDesign(Design.DELAY);
			delay.setIDModel(idFirst);
			transitionSmt2.addConstraint(delay);
		}
		return transitionSmt2;

	}

	protected int getResetID(Transition trans)
	{
		return 0;
	}

	protected void createVariables(List<VariableState> variableListByName)
	{
		if (variableListByName == null)
			return;
		for (VariableState varState : variableListByName)
		{
			String name = varState.getID().replaceAll("sys.", "");
			VariableModel varM = model.parseGlobalVariable(name);
			if (varM == null)
			{
				System.out.println(model.getGlobalDeclaration());
				System.out.println("Missing type for " + name);
				continue;
			}
			// System.out.println(name);
			VariableSmt2 var2 = new VariableSmt2(name, varM.getType(), varState.getValue(), 1, null);
			currentState.addVariable(var2);
			varList.add(var2);
		}
	}

	ConstraintSmt2 transProp(ConstraintModel con, Model model)
	{
		con.setModel(model);
		ConstraintInterface prop = con.parseConstraint(null);
		//
		// String text = ConstraintModel.getConstraintText(prop);
		// System.out.println(text);

		prop = filterConstraint(prop);
		// if (guard.compareTo("1") == 0)
		if (prop == null)
			return null;

		TextSmt2 conver = convertConstraint2SMT2(prop, currentState, null, zoneCounter - 1, true, 0, 0);
		if (conver == null)
		{
			String text2 = ConstraintModel.getConstraintText(prop);
			System.out.println("Warning: Property was not parsed " + text2);
			return null;
		}
		ConstraintSmt2 con2 = (ConstraintSmt2) conver;
		con2.setDesign(Design.GUARD);
		return con2;
	}

	@Override
	void createInitial(Trace trace)
	{
		String locs = "";
		for (Process p : trace.getProcessList())
		{
			TemplateModel tm = model.getTemplateByLocationName(p.getName());
			if (tm == null)
				continue;
			Template templ = tm.getTemplate();
			Location loc = templ.getInit();
			String init = p.getName() + "." + loc.getID();
			locs += init + " ";
		}

		LocationVector vec = new LocationVector("vec1", locs);
		trace.addLocationVector(vec);
		Node initial = new Node("State1", "vec1", "", "");
		// NodeVector vec = new NodeVector();
		// vec.set
		trace.setInitialNode(initial);
		// currentState = convertState(node, trans, zoneCounter);

	}

	@Override
	public ModelSmt2 transform(Trace trace, Model model)
	{
		this.model = model;
		if (this.model == null)
		{
			System.out.println("Error: Model was not loaded.");
			return null;
		}

		ModelSmt2 smt2 = super.transform(trace, model);

		// property will not be used
		// todo: perhaps delete
		ConstraintSmt2 ctl = transProp(model.getProperty(0), model);
		if ((ctl != null) && (smt2 != null))
			smt2.addCTLProperty(ctl);

		return smt2;
	}
}
