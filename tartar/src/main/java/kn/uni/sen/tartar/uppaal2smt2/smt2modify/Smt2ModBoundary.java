package kn.uni.sen.tartar.uppaal2smt2.smt2modify;

import java.util.ArrayList;
import java.util.List;

import kn.uni.sen.tartar.uppaal2smt2.SMT2_OPTION;
import kn.uni.sen.tartar.uppaal2smt2.smt2.model.ClockSmt2;
import kn.uni.sen.tartar.uppaal2smt2.smt2.model.ConstantSmt2;
import kn.uni.sen.tartar.uppaal2smt2.smt2.model.ConstraintSmt2;
import kn.uni.sen.tartar.uppaal2smt2.smt2.model.StateSmt2;
import kn.uni.sen.tartar.uppaal2smt2.smt2.model.TextSmt2;
import kn.uni.sen.tartar.uppaal2smt2.smt2.model.TransitionSmt2;
import kn.uni.sen.tartar.uppaal2smt2.smt2.model.VariableSmt2;
import kn.uni.sen.tartar.uppaal2smt2.smt2.model.ConstraintSmt2.Design;

/**
 * Clone the current SMT2 model and add boundary modification
 * 
 * @author Martin Koelbl
 */
public class Smt2ModBoundary extends SMT2Mod
{
	public final static String bName = "_" + SMT2_OPTION.boundary_name;
	List<Integer> counterList = new ArrayList<>();

	public Smt2ModBoundary()
	{
		dub.addStartComment("; boundary modification\n");
		dub.addFileExtra(bName);
	}

	@Override
	protected StateSmt2 cloneState(StateSmt2 state)
	{
		StateSmt2 dubState = stateMap.get(state);
		if (dubState != null)
			return dubState;

		counterList.add(1);
		return super.cloneState(state);
	}

	@Override
	protected void traverseTransition(TransitionSmt2 trans)
	{
		super.traverseTransition(trans);
	}

	boolean isBound(TextSmt2 con)
	{
		if (con.getClass() == ConstantSmt2.class)
			return true;
		if (con.getClass() == VariableSmt2.class)
			return true;
		if (con.getClass() == ConstraintSmt2.class)
		{
			String t = con.getTextSmt2();
			if (t.startsWith("(+") || t.startsWith("(-"))
				return true;
		}
		return false;
	}

	@Override
	protected ConstraintSmt2 cloneConstraint(ConstraintSmt2 con, StateSmt2 dupFrom, StateSmt2 dupTo)
	{
		// System.out.println(con.getTextSmt2());
		ConstraintSmt2 dupCon = new ConstraintSmt2(con.getOperator());
		dupCon.setDesign(con.getDesign());
		for (int i = 0; i < con.getConSize(); i++)
		{
			TextSmt2 con_i = cloneText(con.getCon(i), dupFrom, dupTo);
			dupCon.addCon(con_i);
		}

		// System.out.println(dupCon.getTextSmt2());
		// modify only invariants and guards
		if ((dupCon.getDesign() != Design.INVARIANT) && (dupCon.getDesign() != Design.GUARD))
			return dupCon;

		// clock constraints always contains only two parameters
		if (dupCon.getConSize() != 2)
			return dupCon;

		TextSmt2 dupCon1 = dupCon.getCon(0);
		TextSmt2 dupCon2 = dupCon.getCon(1);

		if (dupCon.getOperator().compareTo("&&") == 0)
		{
			dupCon = new ConstraintSmt2(con.getOperator());
			dupCon.setDesign(con.getDesign());
			dupCon.setID(con.getID());
			if (dupCon1 instanceof ConstraintSmt2)
			{
				((ConstraintSmt2) dupCon1).setDesign(dupCon.getDesign());
				((ConstraintSmt2) dupCon1).setID(dupCon.getID());
				dupCon1 = cloneConstraint((ConstraintSmt2) dupCon1, dupFrom, dupTo);
			}
			if (dupCon2 instanceof ConstraintSmt2)
			{
				((ConstraintSmt2) dupCon2).setDesign(dupCon.getDesign());
				((ConstraintSmt2) dupCon2).setID(dupCon.getID());
				dupCon2 = cloneConstraint((ConstraintSmt2) dupCon2, dupFrom, dupTo);
			}
			dupCon.addCon(dupCon1);
			dupCon.addCon(dupCon2);
			return dupCon;
		}

		// modify only bound comparison values of form "clock
		// comparison-operator bound"
		if (!!!isBound(dupCon2))
			return dupCon;

		// get current clock in first parameter
		ClockSmt2 clock = getClock(dupCon1);
		if (clock == null)
			return dupCon;

		// create new variable
		// int stateCounterSpecial = counterList.get(clock.getIndex() - 1);
		// counterList.set(clock.getIndex() - 1, stateCounterSpecial + 1);
		String varName = clock.getOrigin().replace(".", "_");
		// check if bound variation variable already exists
		// todo: use x-th occurrence of variable varName in whole constraint
		// instead of 1
		VariableSmt2 bv = createUniqueVar(bName, varName, "Real", dupFrom.getIndex(), con.getID(), 1, null);

		// System.out.println(varName + " " + con.getID());
		curState.addVariable(bv);

		// extend constraint
		ConstraintSmt2 con_i = new ConstraintSmt2("+", dupCon2, bv);
		ConstraintSmt2 dubCon = new ConstraintSmt2(dupCon.getOperator(), dupCon1, con_i);
		dubCon.setDesign(dupCon.getDesign());

		// ensure constant with difference is positive
		ConstantSmt2 constant0 = new ConstantSmt2("0.0");
		if (!!!old)
		{
			// ensure comparison is still >=0
			ConstraintSmt2 conj = new ConstraintSmt2(">=", con_i, constant0);
			// soft-assert modification
			ConstraintSmt2 conSoft = new ConstraintSmt2("=", bv, constant0);
			conSoft.setSoft(true);
			if (dupTo == null)
			{
				curState.addConstraint(conj);
				curState.addConstraint(conSoft);
			} else
			{
				curTrans.addConstraint(conj);
				curState.addConstraint(conSoft);
			}
		}

		return dubCon;
	}
}
