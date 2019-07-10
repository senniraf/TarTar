package kn.uni.sen.tartar.uppaal2smt2.smt2modify;

import java.util.ArrayList;
import java.util.List;

import kn.uni.sen.tartar.uppaal2smt2.SMT2_OPTION;
import kn.uni.sen.tartar.uppaal2smt2.Transformer;
import kn.uni.sen.tartar.uppaal2smt2.smt2.model.ClockSmt2;
import kn.uni.sen.tartar.uppaal2smt2.smt2.model.ConstantSmt2;
import kn.uni.sen.tartar.uppaal2smt2.smt2.model.ConstraintSmt2;
import kn.uni.sen.tartar.uppaal2smt2.smt2.model.StateSmt2;
import kn.uni.sen.tartar.uppaal2smt2.smt2.model.TextSmt2;
import kn.uni.sen.tartar.uppaal2smt2.smt2.model.VariableSmt2;
import kn.uni.sen.tartar.uppaal2smt2.smt2.model.ConstraintSmt2.Design;

/**
 * Clone the current SMT2 model and add clock reference modification
 * 
 * @author Martin Koelbl
 */
public class Smt2ModReference extends SMT2Mod
{
	public final static String bName = "_" + SMT2_OPTION.reference_name;

	public Smt2ModReference()
	{
		dub.addStartComment("; clock switch/reference modification\n");
		dub.addFileExtra(bName);
	}

	protected ConstraintSmt2 cloneConstraint(ConstraintSmt2 con, StateSmt2 dupFrom, StateSmt2 dupTo)
	{
		ConstraintSmt2 dupCon = super.cloneConstraint(con, dupFrom, dupTo);
		if ((dupCon.getDesign() != Design.INVARIANT) && (dupCon.getDesign() != Design.GUARD))
			return dupCon;

		ClockSmt2 clock = getClock(dupCon);
		if (clock == null)
			return dupCon;

		List<VariableSmt2> varList = new ArrayList<>();
		List<ClockSmt2> clockList = dupFrom.getClockList();
		ConstantSmt2 constantDefault = new ConstantSmt2("false");
		// create all soft asserts
		for (ClockSmt2 c : clockList)
		{
			if (c == clock)
				continue;
			if (c.getOrigin().compareTo(Transformer.t0Name) == 0)
				continue;
			String varName = clock.getOrigin().replace(".", "_");
			VariableSmt2 cv = createUniqueVar(bName, varName, "Bool", dupFrom.getIndex(), con.getID(), 1,
					c.getOrigin());

			dupFrom.addVariable(cv);
			varList.add(cv);
			ConstraintSmt2 conSoft = new ConstraintSmt2("=", cv, constantDefault);
			conSoft.setSoft(true);
			addConstraint(conSoft, dupFrom, dupTo);
		}

		// create switch with only one clock
		ConstraintSmt2 xor = createXor(varList);
		if (xor != null)
			addConstraint(xor, dupFrom, dupTo);

		// switch clock
		ConstraintSmt2 select = dupCon;
		int counter = 0;
		for (ClockSmt2 c : clockList)
		{
			if (c == clock)
				continue;
			if (c.getOrigin().compareTo(Transformer.t0Name) == 0)
				continue;
			ConstraintSmt2 con1 = super.cloneConstraint(con, dupFrom, dupTo);
			exchangeClock(con1, clock, c);

			ConstraintSmt2 next = new ConstraintSmt2("ite");
			next.setNewLine(true);
			next.addCon(varList.get(counter++));
			next.addCon(con1);
			next.addCon(select);
			select = next;
		}
		select.setDesign(con.getDesign());
		return select;
	}

	private boolean exchangeClock(ConstraintSmt2 con, ClockSmt2 clock, ClockSmt2 variableSmt2)
	{
		for (int i = 0; i < con.getConSize(); i++)
		{
			TextSmt2 con_i = con.getCon(i);
			if (con_i == clock)
			{
				con.setIndex(i, variableSmt2);
				return true;
			}
			if (con_i instanceof ConstraintSmt2)
				if (exchangeClock((ConstraintSmt2) con_i, clock, variableSmt2))
					return true;
		}
		return false;
	}

	void addConstraint(ConstraintSmt2 con, StateSmt2 dupFrom, StateSmt2 dupTo)
	{

		if (dupTo == null)
		{
			// its an invariant of a state
			dupFrom.addConstraint(con);
			return;
		}
		curTrans.addConstraint(con);
	}
}
