package kn.uni.sen.joblibrary.tartar.web.form;

public class ResultsForm
{
	private String property;
	private boolean allTraces;
	private boolean nonOccurance;
	private boolean probability;
	private boolean extraInformation;
	
	private String depth;
	private String time;

	// Save Options.
	
	public String getProperty()
	{
		return property;
	}

	public void setProperty(String property)
	{
		this.property = property;
	}
	

	public void setAllTraces(boolean allTraces)
	{
		this.allTraces = allTraces;
	}

	public boolean getAllTraces()
	{
		return allTraces;
	}
	
	public void setNonOccurance(boolean nonOccurance)
	{
		this.nonOccurance = nonOccurance;
	}

	public boolean getNonOccurance()
	{
		return nonOccurance;
	}

	public void setProbability(boolean probability)
	{
		this.probability = probability;
	}

	public boolean getProbability()
	{
		return probability;
	}
		
	public void setExtraInformation(boolean extraInformation)
	{
		this.extraInformation = extraInformation;
	}

	public boolean getExtraInformation()
	{
		return extraInformation;
	}
	
	public String getDepth()
	{
		return depth;
	}

	public void setDepth(String depth)
	{
		this.depth = depth;
	}

	public String getTime()
	{
		return time;
	}

	public void setTime(String time)
	{
		this.time = time;
	}
	
}
