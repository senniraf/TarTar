package kn.uni.sen.joblibrary.tartar.convert;

import kn.uni.sen.jobscheduler.common.model.JobEvent;
import kn.uni.sen.jobscheduler.common.model.RunContext;

public class Transformer
{
	protected String fileExtra = "";
	protected String variant = "";
	protected RunContext jobContext;
	int commentDepth = 1;

	protected final static String start = "; UPPAAL symbolic trace to smt2 translation (Version " + Ut2Smt2.version
			+ ")\n";
	public final static String t0Name = "_d";

	public Transformer(RunContext jobContext)
	{
		this.jobContext = jobContext;
	}

	public String getVariant()
	{
		return variant;
	}

	public String getFileExtra()
	{
		return fileExtra;
	}

	public String comment(int depth, String comment)
	{
		jobContext.logEventStatus(JobEvent.DEBUG, comment);
		if(depth > commentDepth)
			return "";
		// commentDepth == 0 -> no comments
		// commentDepth == 1 -> state and transition names
		// commentDepth == 2 -> reason for properties
		// commentDepth == 3 -> original source text
		return comment;
	}

	public void setFileExtra(String string)
	{
		fileExtra = string;
	}
}
