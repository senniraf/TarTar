package kn.uni.sen.joblibrary.tartar.convert.smt2modify;

import kn.uni.sen.joblibrary.tartar.common.SMT2_OPTION;
import kn.uni.sen.joblibrary.tartar.convert.Transformer;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.ConstantSmt2;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.ConstraintSmt2;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.StateSmt2;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.VariableSmt2;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.ConstraintSmt2.Design;

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
		ConstraintSmt2 or = new ConstraintSmt2("or");
		int count = 0;
		for (int id : dupState.getFileID())
		{
			String idState = dupState.getUppaalID().get(count);
			count++;
			VariableSmt2 uv = createUniqueVar(bName, idState + "_", "Bool", dupState.getIndex(), id, 0, null);
			dupState.addVariable(uv);
			// System.out.print(id + " " + uv.getName() + "\n");

			ConstantSmt2 constantDefault = new ConstantSmt2("false");
			if (dupState.isUrgent())
			{
				constantDefault = new ConstantSmt2("true");
				dupState.setUrgent(false);
			}
			or.addCon(uv);

			ConstraintSmt2 conSoft = new ConstraintSmt2("=", uv, constantDefault);
			conSoft.setSoft(true);
			if (!!!old)
				dupState.addConstraint(conSoft);
			//String text = conSoft.getTextSmt2();
			//System.out.print(text);
			//System.out.print("");
		}
		//System.out.println("");

		VariableSmt2 clock = dupState.getVariableByName(Transformer.t0Name + dupState.getIndex());
		ConstantSmt2 constant0 = new ConstantSmt2("0");
		ConstantSmt2 constantTrue = new ConstantSmt2("true");
		ConstraintSmt2 urgentState = new ConstraintSmt2("=", clock, constant0);
		ConstraintSmt2 urgentCon = new ConstraintSmt2("ite", or, urgentState, constantTrue);
		urgentCon.setDesign(Design.URGENT);
		return urgentCon;
	}
}
