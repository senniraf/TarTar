package kn.uni.sen.joblibrary.tartar.gui;

import java.util.ArrayList;
import java.util.List;

import kn.uni.sen.joblibrary.tartar.common.SMT2_OPTION;

public class RunParameter
{
	boolean BExperiment = false;
	String ModelPath;
	String TracePath;
	List<SMT2_OPTION> optionList = new ArrayList<>();
	SMT2_OPTION repair;
	SMT2_OPTION seed;

	public void setExperiment(boolean exp)
	{
		BExperiment = exp;
	}

	public void setModelFile(String modelPath)
	{
		this.ModelPath = modelPath;
	}

	public void setTraceFile(String tracePath)
	{
		this.TracePath = tracePath;
	}

	public void setOption(SMT2_OPTION option)
	{
		optionList.add(option);
	}

	public void setRepair(SMT2_OPTION option)
	{
		repair = option;
	}

	public SMT2_OPTION getRepair()
	{
		return repair;
	}

	public void setSeed(SMT2_OPTION option)
	{
		seed = option;
	}

	public SMT2_OPTION getSeed()
	{
		return seed;
	}

	public List<SMT2_OPTION> getOptionList()
	{
		return optionList;
	}

	public String getModelFile()
	{
		return ModelPath;
	}

	public String getTraceFile()
	{
		return TracePath;
	}

	public boolean isExperiment()
	{
		return BExperiment;
	}
}
