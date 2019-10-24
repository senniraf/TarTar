package kn.uni.sen.joblibrary.tartar.convert.smt2modify;

import java.util.List;

import kn.uni.sen.joblibrary.tartar.convert.smt2.model.ClockSmt2;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.ModelSmt2;

/**
 * Modify variable names of current SMT2 model
 * 
 * @author Martin Koelbl
 */
public class Smt2ModVarName
{
	public ModelSmt2 createTrace(ModelSmt2 smt2Modify, String text)
	{
		List<ClockSmt2> varList = smt2Modify.getClockList();

		for (ClockSmt2 var : varList)
		{
			String name = var.getOrigin();
			if (name.startsWith("_bv"))
				continue;
			// System.out.println(name);
			var.setOrigin(name + text);
		}
		return smt2Modify;
	}
}
