package kn.uni.sen.joblibrary.tartar.convert.smt2modify;

import java.util.ArrayList;
import java.util.List;

import kn.uni.sen.joblibrary.tartar.common.SMT2_OPTION;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.ClockSmt2;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.ConstantSmt2;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.ConstraintSmt2;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.StateSmt2;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.TextSmt2;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.VariableSmt2;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.ConstraintSmt2.Design;

/**
 * Clone the current SMT2 model and add comparison operator modification
 * 
 * @author Martin Koelbl
 */
public class Smt2ModComparison extends SMT2Mod
{
	public final static String bName = "_" + SMT2_OPTION.operator_name;
	// int count_so = 1;

	public final static String[] opList = { "<=", ">=", "<", "=", ">",  };
	public final static String[] nameList = { "se", "ge", "s", "e", "g" };
	// int counter = 1;

	public Smt2ModComparison()
	{
		dub.addStartComment("; operator comparison modification\n");
		dub.addFileExtra(bName);
	}

	protected ConstraintSmt2 cloneConstraint(ConstraintSmt2 con, StateSmt2 dupFrom, StateSmt2 dupTo)
	{
		ConstraintSmt2 dupCon = super.cloneConstraint(con, dupFrom, dupTo);
		if ((dupCon.getDesign() != Design.INVARIANT) && (dupCon.getDesign() != Design.GUARD))
			return dupCon;

		VariableSmt2 var = getVariable(dupCon);
		if (var == null)
			return dupCon;

		// constraint contains one of the comparison operators
		String op = dupCon.getOperator();
		boolean contained = false;
		for (String o : opList)
			if (op.compareTo(o) == 0)
			{
				op = o;
				contained = true;
				break;
			}
		if (!!!contained)
			return dupCon;

		TextSmt2 dupCon1 = dupCon.getCon(0);
		TextSmt2 dupCon2 = dupCon.getCon(1);

		// constraint also contains a clock
		ClockSmt2 clock = getClock(dupCon1);
		if (clock == null)
			clock = getClock(dupCon2);
		if (clock == null)
			return dupCon;

		// create soft asserts
		String varName = clock.getOrigin().replace(".", "_");

		// int count = this.count_so++;
		List<VariableSmt2> varList = new ArrayList<>();
		ConstantSmt2 constantDefault = new ConstantSmt2("false");
		for (int i = 0; i < opList.length; i++)
		{
			// increment l for original comparison operation
			VariableSmt2 ov = createUniqueVar(bName, varName, "Bool", dupFrom.getIndex(), con.getID(), 1, nameList[i]);
			if (opList[i] == op)
				continue;
			dupFrom.addVariable(ov);
			varList.add(ov);
			ConstraintSmt2 conSoft = new ConstraintSmt2("=", ov, constantDefault);
			conSoft.setSoft(true);
			addConstraint(conSoft, dupFrom, dupTo);
		}

		// create possible selection of any operator
		ConstraintSmt2 xor = createXor(varList);
		if (xor != null)
			addConstraint(xor, dupFrom, dupTo);

		// only one operator can be selected
		ConstraintSmt2 select = dupCon;
		int counter = 0;
		for (int i = 0; i < opList.length; i++)
		{
			if (opList[i] == op)
				continue;
			ConstraintSmt2 con1 = super.cloneConstraint(con, dupFrom, dupTo);
			con1.setOperator(opList[i]);

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

	private VariableSmt2 getVariable(TextSmt2 con)
	{
		if (con instanceof VariableSmt2)
			return (VariableSmt2) con;

		if (!!!(con instanceof ConstraintSmt2))
			return null;

		ConstraintSmt2 con2 = (ConstraintSmt2) con;
		for (int i = 0; i < con2.getConSize(); i++)
		{
			VariableSmt2 var = getVariable(con2.getCon(i));
			if (var != null)
				return var;
		}
		return null;
	}

	public static String getOperation(String opName)
	{
		if (opName == null)
			return null;
		for (int i = 0; i < nameList.length; i++)
		{
			if (nameList[i].compareTo(opName) == 0)
				return opList[i];
		}
		return null;
	}
}
