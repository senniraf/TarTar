package kn.uni.sen.joblibrary.tartar.convert.smt2modify;

import kn.uni.sen.joblibrary.tartar.common.SMT2_OPTION;
import kn.uni.sen.joblibrary.tartar.convert.Transformer;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.ClockSmt2;
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
public class Smt2ModReset extends SMT2Mod
{
	public final static String bName = "_" + SMT2_OPTION.reset_name;

	public Smt2ModReset()
	{
		dub.addStartComment("; clock reset modification\n");
		dub.addFileExtra(bName);
	}

	protected ConstraintSmt2 cloneConstraint(ConstraintSmt2 con, StateSmt2 dupFrom, StateSmt2 dupTo)
	{
		ConstraintSmt2 dupCon = super.cloneConstraint(con, dupFrom, dupTo);
		if (dupCon.getDesign() != Design.DELAY)
			return dupCon;

		ClockSmt2 clockTo = (ClockSmt2) con.getCon(0);
		ClockSmt2 clockDif = dupFrom.getClock(Transformer.t0Name, clockTo.getIndex() - 1);
		ClockSmt2 clockFrom = dupFrom.getClock(clockTo.getOrigin(), clockTo.getIndex() - 1);

		// todo: handle also the other locations
		Integer id = con.getIDModel();
		//Integer id2 = con.getIDModel();

		String varName = clockTo.getOrigin().replace(".", "_");
		
		VariableSmt2 rv = createUniqueVar(bName, varName, "Bool", dupFrom.getIndex() + 1, id, 0, null);
		//System.out.println(rv.getName());

		dupFrom.addVariable(rv);

		ConstraintSmt2 incClock = new ConstraintSmt2("+", clockFrom, clockDif);
		// todo clock should be clock of next state
		ConstraintSmt2 noReset = new ConstraintSmt2("=", clockTo, incClock);

		ConstantSmt2 constant0 = new ConstantSmt2("0");
		ConstraintSmt2 reset = new ConstraintSmt2("=", clockTo, constant0);
		ConstraintSmt2 iteCon = new ConstraintSmt2("ite", rv, reset, noReset);
		iteCon.setDesign(Design.DELAY);
		curTrans.addConstraint(iteCon);

		ConstantSmt2 constantDefault = new ConstantSmt2("false");
		if (curTrans.isReset(clockTo))
			constantDefault = new ConstantSmt2("true");

		ConstraintSmt2 conSoft = new ConstraintSmt2("=", rv, constantDefault);
		conSoft.setSoft(true);

		return conSoft;
	}
}
