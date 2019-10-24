package kn.uni.sen.joblibrary.tartar.convert.smt2modify;

public class VariationValue
{
	String variation;
	String clock_name;
	int trace_step;

	// index l in smt code
	int clock_index_l;
	String end;

	int id; // state or transition id of uppaal model
	// index give the occurrence of this clock in guard/transition
	int id_index;

	public VariationValue(String op, String varName, int step, int id, int id_index, int l, String end)
	{
		variation = op;
		clock_name = varName;
		trace_step = step;
		this.id = id;
		this.id_index = id_index;
		clock_index_l = l;
		this.end = end;
	}

	public boolean equalMod(String op, String varName, int step, int id, int id_index, String end)
	{
		if (variation.compareTo(op) != 0)
			return false;
		if (clock_name.compareTo(varName) != 0)
			return false;
		if ((this.id != id) || (this.id_index != id_index))
			return false;
		if (!!!compareEnd(this.end, end))
			return false;
		return true;
	}

	public static boolean compareEnd(String end, String end2)
	{
		if (end2 != end)
		{
			if ((end == null) || (end2 == null))
				return false;
			if (end.compareTo(end2) != 0)
				return false;
		}
		return true;
	}
}
