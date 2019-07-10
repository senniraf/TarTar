package kn.uni.sen.tartar.gui;

import java.util.ArrayList;
import java.util.List;

import kn.uni.sen.tartar.uppaal2smt2.SMT2_OPTION;

public class RunParameter
{
	boolean BExperiment = false;
	String ModelPath;
	String TracePath;
	List<SMT2_OPTION> optionList = new ArrayList<>();

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
