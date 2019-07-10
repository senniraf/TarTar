package kn.uni.sen.tartar.admissible;

import java.util.ArrayList;
import java.util.List;

public class Repair
{
	List<ModifiedConstraint> constraintList = new ArrayList<>();
	ResultAdm admissible;
	long repairTime;
	long admTime;

	public void addModification(ModifiedConstraint modCon)
	{
		constraintList.add(modCon);
	}

	public List<ModifiedConstraint> getModificationList()
	{
		return constraintList;
	}

	public boolean isAdmissible()
	{
		if (admissible == null)
			return false;
		return admissible.trace == null;
	}

	public void setAdmissible(ResultAdm b)
	{
		admissible = b;
	}

	public String getModificationText()
	{
		String text = "";
		boolean first = true;
		for (ModifiedConstraint con : constraintList)
		{

			if (!!!first)
				text += ", ";
			first = false;
			text += con.getOrginalConstraint() + " -> " + con.getModifiedConstraint();
		}
		return text;
	}

	public List<String> getCounterTrace()
	{
		if (admissible == null)
			return new ArrayList<>();
		return admissible.trace;
	}

	public void setTimeRepair(long repairTime)
	{
		this.repairTime = repairTime;
	}

	public long getTimeRepair()
	{
		return this.repairTime;
	}

	public void setTimeAdm(long admTime)
	{
		this.admTime = admTime;
	}

	public long getTimeAdm()
	{
		return this.admTime;
	}
}
