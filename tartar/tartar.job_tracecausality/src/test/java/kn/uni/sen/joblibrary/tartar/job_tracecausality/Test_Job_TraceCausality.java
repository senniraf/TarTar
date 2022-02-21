package kn.uni.sen.joblibrary.tartar.job_tracecausality;

import static org.junit.Assert.assertTrue;

import kn.uni.sen.jobscheduler.common.JobAbstractTest;
import kn.uni.sen.jobscheduler.common.model.Job;
import kn.uni.sen.jobscheduler.common.model.ResourceInterface;
import kn.uni.sen.jobscheduler.common.resource.ResourceFile;

public class Test_Job_TraceCausality extends JobAbstractTest
{
	String modelFile = "busstop.xml";
	{
		modelFile = "fischer_bad.xml";
		modelFile = "0db2.xml";
	}

	@Override
	protected Job createJob()
	{
		return new Job_TraceCausality(this);
	}

	@Override
	protected ResourceInterface getResourceByName(String name, boolean out)
	{
		if (Job_TraceCausality.RES_MODEL.equals(name))
		{
			ResourceFile resFile = loadFile(modelFile);
			assertTrue(resFile != null);
			return resFile;
		}
		return null;
	}

	public static void main(String args[])
	{
		(new Test_Job_TraceCausality()).testAll();
	}
}
