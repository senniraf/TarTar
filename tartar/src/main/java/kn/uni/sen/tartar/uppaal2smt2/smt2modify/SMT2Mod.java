package kn.uni.sen.tartar.uppaal2smt2.smt2modify;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import kn.uni.sen.tartar.uppaal2smt2.smt2.model.ClockSmt2;
import kn.uni.sen.tartar.uppaal2smt2.smt2.model.ConstraintSmt2;
import kn.uni.sen.tartar.uppaal2smt2.smt2.model.TextSmt2;
import kn.uni.sen.tartar.uppaal2smt2.smt2.model.VariableSmt2;

/**
 * Contains necessary structures for modifications/variations of clock
 * constraints
 * 
 * @author Martin Koelbl
 */
public class SMT2Mod extends Smt2Clone
{
	public class VariationSmt2
	{
		String variation;
		String clock_name;
		int trace_step;
		int clock_index_l;
		String end;

		public VariationSmt2(String op, String varName, int step, int l, String end)
		{
			variation = op;
			clock_name = varName;
			trace_step = step;
			clock_index_l = l;
			this.end = end;
		}
	}

	// contains already created repair variations
	List<VariationValue> variationList = new ArrayList<>();
	// contains current counter for index l of a clock
	List<VariationSmt2> clockIndexList = new ArrayList<>();
	// contain variation variables
	HashMap<VariationValue, VariableSmt2> variableList = new HashMap<>();

	public SMT2Mod()
	{
		//reduceLength = 1;
	}

	private VariationValue getClockVariation(String op, String varName, int step, int id, int id_index, String end)
	{
		VariationValue varVal = null;
		for (VariationValue s : variationList)
		{
			// use same string value for equivalent string content
			if (s.equalMod(op, varName, step, id, id_index, end))
				return s;
		}
		int l = 0;
		if (clockIndexList != null)
		{
			// op varName step
			for (VariationSmt2 v2 : clockIndexList)
				if ((v2.variation.compareTo(op) == 0) && (v2.clock_name.compareTo(varName) == 0)
						&& (v2.trace_step == step) && (VariationValue.compareEnd(v2.end, end)))
				{
					l = ++v2.clock_index_l;
					break;
				}
			if (l == 0)
			{
				l = 1;
				clockIndexList.add(new VariationSmt2(op, varName, step, l, end));
			}
		}
		varVal = new VariationValue(op, varName, step, id, id_index, l, end);
		variationList.add(varVal);
		return varVal;
	}

	// ugly, but fast
	boolean old = false;

	protected VariableSmt2 createUniqueVar(String op, String varName, String type, int step, int id, int id_index,
			String end)
	{
		// String name = VariableSmt2.getName(varName, step, id);
		VariationValue varVal = getClockVariation(op, varName, step, id, id_index, end);
		VariableSmt2 var = variableList.get(varVal);
		old = true;
		if (var == null)
		{
			old = false;
			String name = op + "_" + varName;
			if (end == null)
				end = "";
			else
				end = "_" + end;
			if (varVal.clock_index_l > 0)
				end = varVal.clock_index_l + end;
			var = new VariableSmt2(name, type, null, step, end);

			String com = null;
			if (varVal.id > 0)
				com = "" + varVal.id;
			if (varVal.id_index > 0)
				com += (com == null ? "" : "_") + varVal.id_index;
			var.setComment(com);
			variableList.put(varVal, var);
		}
		return var;
	}

	protected ClockSmt2 getClock(TextSmt2 con)
	{
		if (con instanceof ClockSmt2)
			return (ClockSmt2) con;

		if (!!!(con instanceof ConstraintSmt2))
			return null;

		ConstraintSmt2 con2 = (ConstraintSmt2) con;
		for (int i = 0; i < con2.getConSize(); i++)
		{
			ClockSmt2 var = getClock(con2.getCon(i));
			if (var != null)
				return var;
		}
		return null;
	}

	protected ConstraintSmt2 createXor(List<VariableSmt2> varList)
	{
		if (varList.size() <= 1)
			return null;

		ConstraintSmt2 single = new ConstraintSmt2("and");
		single.setNewLine(true);
		for (int j = 0; j < varList.size(); j++)
		{
			VariableSmt2 v1 = varList.get(j);
			for (int i = j; i < varList.size(); i++)
			{
				VariableSmt2 v2 = varList.get(i);
				if (v1 == v2)
					continue;
				ConstraintSmt2 and = new ConstraintSmt2("and");
				and.addCon(v1);
				and.addCon(v2);
				ConstraintSmt2 not = new ConstraintSmt2("not");
				not.addCon(and);
				single.addCon(not);
			}
		}
		return single;
	}
}
