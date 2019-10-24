package kn.uni.sen.joblibrary.tartar.job_repaircomputation;

import java.util.ArrayList;
import java.util.List;

import kn.uni.sen.joblibrary.tartar.common.ResultAdm;
import kn.uni.sen.joblibrary.tartar.modifymodel.ModifiedConstraint;

public class Repair
{
	String fileRepaired = null;
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

	public String getRepairedFile()
	{
		return fileRepaired;
	}

	public void setRepairedFile(String file)
	{
		fileRepaired = file;
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
