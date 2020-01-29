package kn.uni.sen.joblibrary.tartar.modifymodel;

import java.util.ArrayList;
import java.util.List;

import kn.uni.sen.joblibrary.tartar.job_repaircomputation.Repair;

public class Fault
{
	String fault;
	List<Repair> repairList = new ArrayList<>();
	List<String> changeList = new ArrayList<>();
	List<String> changeAdmList = new ArrayList<>();
	double memory = 0.0;
	double memoryZ3 = 0.0;
	int admissibleCount = 0;
	int lengthTrace;
	int varCount = 0;
	int assertCount = 0;
	long timeUppal = 0;
	long timeQE = 0;

	public Fault(String fault, long timeMS)
	{
		this.fault = fault;
		this.timeUppal = timeMS;
	}

	public String getFault()
	{
		return fault;
	}

	public void addRepair(Repair repair)
	{
		if (repair == null)
			return;
		if (repairList.contains(repair))
			return;
		if (repair.isAdmissible())
			admissibleCount++;
		repairList.add(repair);
		addModList(repair.getModificationList());
		if(repair.isAdmissible())
			addModAdmList(repair.getModificationList());
	}

	private void addModList(List<ModifiedConstraint> modList)
	{
		for (ModifiedConstraint mod : modList)
		{
			if (mod == null)
				continue;
			boolean found = false;
			String n = mod.getName();
			for (String s : changeList)
				if (s.equals(n))
				{
					found = true;
					break;
				}
			if (found)
				continue;
			changeList.add(n);
		}
	}
	
	private void addModAdmList(List<ModifiedConstraint> modList)
	{
		for (ModifiedConstraint mod : modList)
		{
			if (mod == null)
				continue;
			boolean found = false;
			String n = mod.getName();
			for (String s : changeAdmList)
				if (s.equals(n))
				{
					found = true;
					break;
				}
			if (found)
				continue;
			changeAdmList.add(n);
		}
	}

	public List<String> getChangeList()
	{
		return changeList;
	}
	
	public List<String> getChangeAdmList()
	{
		return changeAdmList;
	}

	public void setMemory(double memory)
	{
		this.memory = memory;
	}

	public void setMemoryZ3(double maxZ3)
	{
		this.memoryZ3 = maxZ3;
	}

	int getRepairCount()
	{
		return repairList.size();
	}

	int getAdmissibleCount()
	{
		return admissibleCount;
	}

	public double getMaxMemory()
	{
		return memory;
	}

	public double getMaxMemoryZ3()
	{
		return memoryZ3;
	}

	public long getTimeAdmMax()
	{
		long max = 0;
		for (Repair rep : repairList)
			if (rep.getTimeAdm() > max)
				max = rep.getTimeAdm();
		return max;
	}

	public long getTimeRepairMax()
	{
		long max = 0;
		for (Repair rep : repairList)
			if (rep.getTimeRepair() > max)
				max = rep.getTimeRepair();
		return max;
	}

	public boolean hasAdmissibleRepair()
	{
		for (Repair rep : repairList)
			if (rep.isAdmissible())
				return true;
		return false;
	}

	public void setMaxTraceLength(int length)
	{
		lengthTrace = length;
	}

	public int getMaxTraceLength()
	{
		return lengthTrace;
	}

	public long getUppaalTime()
	{
		return timeUppal;
	}

	public void setTimeQE(long time)
	{
		timeQE = time;
	}

	public long getTimeQE()
	{
		return timeQE;
	}

	public boolean isQETimeout()
	{
		return timeQE < 0;
	}

	public void setVarZ3(int varCount)
	{
		this.varCount = varCount;
	}

	public int getVarZ3()
	{
		return this.varCount;
	}

	public void setAssertZ3(int assertCount)
	{
		this.assertCount = assertCount;
	}

	public int getAssertZ3()
	{
		return this.assertCount;
	}

	public List<Repair> getRepairList()
	{
		return repairList;
	}

	public long getTimeAdm()
	{
		long val = 0;
		for (Repair rep : getRepairList())
			val += rep.getTimeAdm();
		return val;
	}

	public long getTimeRepair()
	{
		long val = 0;
		for (Repair rep : getRepairList())
			val += rep.getTimeRepair();
		return val;
	}

	public Repair getRepairByIndex(int index)
	{
		if (repairList.size() <= index)
			return null;
		return repairList.get(index);
	}
}
