package kn.uni.sen.joblibrary.tartar.convert.smt2modify;

import java.util.HashMap;
import java.util.List;

import kn.uni.sen.joblibrary.tartar.convert.smt2.model.ClockSmt2;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.ConstantSmt2;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.ConstraintSmt2;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.ModelSmt2;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.StateSmt2;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.TextSmt2;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.TransitionSmt2;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.VariableSmt2;

/**
 * Traverses one time a SMT2 model
 * 
 * @author Martin Koelbl
 */
public class Smt2Clone extends Smt2Traverse
{
	HashMap<StateSmt2, StateSmt2> stateMap = new HashMap<>();

	ModelSmt2 dub = new ModelSmt2();

	TransitionSmt2 curTrans;
	StateSmt2 curState;

	public ModelSmt2 createTrace(ModelSmt2 origin)
	{
		dub.addStartComment(origin.getStartComment());
		dub.addFileExtra(origin.getFileExtra());
		dub.addCTLProperty(origin.getCTLProperty());
		traverse(origin);
		return dub;
	}

	@Override
	protected void traverseName(String modelName)
	{
		dub.setModelName(modelName);
	}

	@Override
	protected void traverseVariable(VariableSmt2 var)
	{
		dub.addVariable(cloneVariable(var));
	}

	protected VariableSmt2 cloneVariable(VariableSmt2 var)
	{
		if (var instanceof ClockSmt2)
		{
			ClockSmt2 clock = (ClockSmt2) var;
			ClockSmt2 dubclock = new ClockSmt2(var.getOrigin(), clock.getIndex());
			dubclock.setExtra(clock.isExtra());
			dubclock.setComment(clock.getComment());
			dubclock.setLastSetStep(clock.getLastSetStep());
			return dubclock;
		}
		VariableSmt2 var2 = new VariableSmt2(var.getOrigin(), var.getType(), var.getValue(), var.getIndex(),
				var.getNameEnd());
		var2.setComment(var.getComment());
		var2.setConstant(var.getConstant());
		var2.setLastSetStep(var.getLastSetStep());
		var2.setDefine(var.getDefine());
		return var2;
	}

	@Override
	protected void traverseInitial(StateSmt2 initialState)
	{
		dub.setInitialState(cloneState(initialState));
	}

	@Override
	protected void traverseTransition(TransitionSmt2 trans)
	{
		StateSmt2 dubFrom = cloneState(trans.getFrom());
		StateSmt2 dubTo = cloneState(trans.getTo());

		TransitionSmt2 dubTrans = new TransitionSmt2(trans.getName(), dubFrom, dubTo);
		List<ClockSmt2> list = trans.getResetList();
		if (list != null)
			for (ClockSmt2 c : list)
			{
				ClockSmt2 c2 = (ClockSmt2) cloneText(c, dubFrom, dubTo);
				dubTrans.addReset(c2);
			}

		curTrans = dubTrans;
		dubTrans.addFromName(trans.getFromName());
		dubTrans.addToName(trans.getToName());
		for (ClockSmt2 clock : trans.getFrom().getClockList())
			if (trans.isReset(clock))
			{
				ClockSmt2 dupClock = (ClockSmt2) dubFrom.getVariableByName(clock.getName());
				dubTrans.addReset(dupClock);
			}
		for (ConstraintSmt2 con : trans.getConstraintList())
		{
			dubTrans.addConstraint(cloneTransitionGuard(con, dubFrom, dubTo));
		}
		dub.addTransition(dubTrans);
	}

	protected StateSmt2 cloneState(StateSmt2 state)
	{
		StateSmt2 dubState = stateMap.get(state);
		if (dubState != null)
			return dubState;

		dubState = new StateSmt2(state.getIndex());
		for (Integer upID : state.getFileID())
			dubState.addFileID(upID);
		for (String upID : state.getUppaalID())
			dubState.addUppaalID(upID);
		curState = dubState;
		dubState.setUrgent(state.isUrgent());
		dubState.setLocationList(state.getLocationList());
		for (VariableSmt2 var : state.getVariableList())
			dubState.addVariable(cloneVariable(var));

		for (ConstraintSmt2 con : state.getConstraintList())
			dubState.addConstraint(cloneInvariantConstraint(con, dubState));

		stateMap.put(state, dubState);
		return dubState;
	}

	protected TextSmt2 cloneText(TextSmt2 con, StateSmt2 dubFrom, StateSmt2 dubTo)
	{
		if (con instanceof ConstraintSmt2)
		{
			ConstraintSmt2 oCon = (ConstraintSmt2) con;

			ConstraintSmt2 dupCon = new ConstraintSmt2(oCon.getOperator());
			dupCon.setDesign(oCon.getDesign());
			dupCon.setNewLine(oCon.getNewLine());
			for (int i = 0; i < oCon.getConSize(); i++)
			{
				TextSmt2 con_i = cloneText(oCon.getCon(i), dubFrom, dubTo);
				dupCon.addCon(con_i);
			}
			return dupCon;
		} else if (con instanceof ConstantSmt2)
		{
			ConstantSmt2 oCon = (ConstantSmt2) con;
			ConstantSmt2 dubCon = new ConstantSmt2(oCon.getTextSmt2());
			return dubCon;
		} else if (con instanceof ClockSmt2)
		{
			for (ClockSmt2 clock : dubFrom.getClockList())
			{
				if (clock.getName().compareTo(((ClockSmt2) con).getName()) == 0)
					return clock;
			}
			if (dubTo != null)
				for (ClockSmt2 clock : dubTo.getClockList())
				{
					if (clock.getName().compareTo(((ClockSmt2) con).getName()) == 0)
						return clock;
				}
			System.out.println("Warning: clock constraints not found: " + ((ClockSmt2) con).getOrigin());
		} else if (con instanceof VariableSmt2)
		{
			VariableSmt2 varOrg = (VariableSmt2) con;
			for (VariableSmt2 var : dubFrom.getVariableList())
			{
				if (var.getName().compareTo(varOrg.getName()) == 0)
					return var;
			}
			if (dubTo != null)
				for (VariableSmt2 var : dubTo.getVariableList())
				{
					if (var.getName().compareTo(varOrg.getName()) == 0)
						return var;
				}
			for (VariableSmt2 var : dub.getAllVariableList())
			{
				if (var.getName().compareTo(varOrg.getName()) == 0)
					return var;
			}

			System.out.println("Warning: Variable not found: " + varOrg.getName());
		}
		System.out.println("Missing");
		return null;
	}

	protected ConstraintSmt2 cloneInvariantConstraint(ConstraintSmt2 con, StateSmt2 state)
	{
		return cloneConstraint(con, state, null);
	}

	protected ConstraintSmt2 cloneTransitionGuard(ConstraintSmt2 con, StateSmt2 dubFrom, StateSmt2 dubTo)
	{
		return cloneConstraint(con, dubFrom, dubTo);
	}

	protected ConstraintSmt2 cloneConstraint(ConstraintSmt2 con, StateSmt2 dupFrom, StateSmt2 dupTo)
	{
		ConstraintSmt2 dupCon = new ConstraintSmt2(con.getOperator());
		dupCon.setDesign(con.getDesign());
		dupCon.setNewLine(con.getNewLine());
		for (int i = 0; i < con.getConSize(); i++)
		{
			// System.out.println(con.getTextSmt2());
			TextSmt2 con_i = cloneText(con.getCon(i), dupFrom, dupTo);
			dupCon.addCon(con_i);
		}
		dupCon.setID(con.getID());
		dupCon.setIDL(con.getIDL());
		dupCon.setIDModel(con.getIDModel());
		dupCon.setSoft(con.isSoft());
		return dupCon;
	}

	@Override
	protected void traverseProperty(ConstraintSmt2 prop)
	{
		// todo: variables are not correctly parsed
		// looks like ugly hack
		// TextSmt2 con0 = prop.getCon(0);
		// if(con0 instanceof ClockSmt2)
		ConstraintSmt2 dupProp = cloneConstraint(prop, null, null);
		dub.addProperty(dupProp);
	}
}
