package kn.uni.sen.tartar.uppaal2smt2.smt2modify;

import kn.uni.sen.tartar.uppaal2smt2.SMT2_OPTION;
import kn.uni.sen.tartar.uppaal2smt2.Transformer;
import kn.uni.sen.tartar.uppaal2smt2.smt2.model.ConstantSmt2;
import kn.uni.sen.tartar.uppaal2smt2.smt2.model.ConstraintSmt2;
import kn.uni.sen.tartar.uppaal2smt2.smt2.model.StateSmt2;
import kn.uni.sen.tartar.uppaal2smt2.smt2.model.VariableSmt2;
import kn.uni.sen.tartar.uppaal2smt2.smt2.model.ConstraintSmt2.Design;

/**
 * Clone the current SMT2 model and add boundary modification
 * 
 * @author Martin Koelbl
 */
public class Smt2ModUrgent extends SMT2Mod
{
	public final static String bName = "_" + SMT2_OPTION.urgent_name;
	boolean foundUrgent = false;

	public Smt2ModUrgent()
	{
		dub.addStartComment("; urgent state modification\n");
		dub.addFileExtra(bName);
		clockIndexList = null;
	}

	protected StateSmt2 cloneState(StateSmt2 state)
	{
		StateSmt2 dubState = stateMap.get(state);
		if (dubState != null)
			return dubState;
		foundUrgent = false;
		curState = super.cloneState(state);
		if (!!!foundUrgent)
		{
			ConstraintSmt2 con = createUrgentConstraint(curState);
			curState.addConstraint(con);
		}
		return curState;
	}

	protected ConstraintSmt2 cloneConstraint(ConstraintSmt2 con, StateSmt2 dupFrom, StateSmt2 dupTo)
	{
		ConstraintSmt2 dupCon = super.cloneConstraint(con, dupFrom, dupTo);
		if (dupCon.getDesign() != Design.URGENT)
			return dupCon;

		foundUrgent = true;
		return createUrgentConstraint(dupFrom);
	}

	ConstraintSmt2 createUrgentConstraint(StateSmt2 dupState)
	{
		// todo: handle also the other locations
		Integer id = dupState.getUppaalID().get(0);

		VariableSmt2 uv = createUniqueVar(bName, "", "Bool", dupState.getIndex(), id, 0, null);
		dupState.addVariable(uv);

		VariableSmt2 clock = dupState.getVariableByName(Transformer.t0Name + dupState.getIndex());

		ConstantSmt2 constantDefault = new ConstantSmt2("false");
		if (dupState.isUrgent())
		{
			constantDefault = new ConstantSmt2("true");
			dupState.setUrgent(false);
		}

		ConstantSmt2 constant0 = new ConstantSmt2("0");
		ConstantSmt2 constantTrue = new ConstantSmt2("true");
		ConstraintSmt2 urgentState = new ConstraintSmt2("=", clock, constant0);
		ConstraintSmt2 urgentCon = new ConstraintSmt2("ite", uv, urgentState, constantTrue);
		urgentCon.setDesign(Design.URGENT);
		dupState.addConstraint(urgentCon);

		ConstraintSmt2 conSoft = new ConstraintSmt2("=", uv, constantDefault);
		conSoft.setSoft(true);
		return conSoft;
	}
}
