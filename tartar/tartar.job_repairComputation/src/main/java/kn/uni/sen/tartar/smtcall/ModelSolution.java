package kn.uni.sen.tartar.smtcall;

import java.util.ArrayList;
import java.util.List;

/**
 * All changed constraints of a solution
 * 
 * @author Martin Koelbl
 */
public class ModelSolution
{
	List<Modification> changeList = new ArrayList<>();

	public boolean equivalent(ModelSolution sol)
	{
		if (contains(sol))
			return true;
		return sol.contains(this);
	}

	public boolean contains(ModelSolution other)
	{
		List<Modification> otherList = other.getChangeList();
		for (Modification v2 : otherList)
		{
			boolean bFound = false;
			for (Modification value : changeList)
			{
				if (v2.isEquivalent(value))
				{
					bFound = true;
					break;
				}
			}
			if (!!!bFound)
				return false;
		}
		return true;
	}

	public List<Modification> getChangeList()
	{
		return changeList;
	}

	public String toText()
	{
		String text = "[";
		boolean first = true;
		for (Modification value : changeList)
		{
			if (!!!first)
				text += ", ";
			first = false;
			text += value.getName() + "=" + value.getValueNew();
		}
		return text + "]";
	}

	public String getAssertText()
	{
		String val = "";
		boolean first = false;
		for (Modification cv : changeList)
		{
			if (!!!first)
			{
				first = true;
				val = cv.getAssertText();
				continue;
			}
			val = "(and " + val + " " + cv.getAssertText() + ")";
		}
		return val;
	}

	public String getAssertNotText()
	{
		String val = "";
		for (Modification cv : changeList)
		{
			String con = "(not " + cv.getAssertText() + ")";
			val += con + "\n";
		}
		return "(and " + val + ")";
	}

	public void addChange(Modification val)
	{
		changeList.add(val);
	}

	public static boolean contained(List<ModelSolution> solList, ModelSolution sol)
	{
		for (ModelSolution oldSol : solList)
			if (oldSol.equivalent(sol))
				return true;
		return false;
	}
}
