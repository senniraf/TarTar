package kn.uni.sen.joblibrary.tartar.job_uppal2smt2.admissible;

import static org.junit.Assert.assertTrue;

import kn.uni.sen.joblibrary.tartar.job_admissibility.Job_Admissibility;
import kn.uni.sen.jobscheduler.common.JobAbstractTest;
import kn.uni.sen.jobscheduler.common.JobDataTest;
import kn.uni.sen.jobscheduler.common.TestResult;
import kn.uni.sen.jobscheduler.common.model.Job;
import kn.uni.sen.jobscheduler.common.resource.ResourceBool;
import kn.uni.sen.jobscheduler.common.resource.ResourceFile;
import kn.uni.sen.jobscheduler.common.resource.ResourceInterface;

public class Test_Job_Admissiblity extends JobAbstractTest
{
	String file1 = "3state.xml";
	String file2 = "4state.xml";
	
	{
		//logger.setVerbose(3);
	}

	@Override
	protected Job createJob()
	{
		return new Job_Admissibility(context.handler());
	}

	@Override
	protected JobDataTest createTest(Job jobTest2, int index)
	{
		if (index > 2)
			return null;
		JobDataTest test = new JobDataTest();
		ResourceFile file = null;
		if (index == 1)
		{
			file = loadFile(file1);
			test.addTest(new TestResult()
			{
				@Override
				public boolean checkResult(Job job)
				{
					ResourceBool res = job.getResourceWithType("Admissible", true, ResourceBool.class);
					assertTrue(res.getDataValue());
					return true;
				}
			});
		} else
		{
			file = loadFile(file2);
			test.addTest(new TestResult()
			{
				@Override
				public boolean checkResult(Job job)
				{
					ResourceBool res = job.getResourceWithType("Admissible", true, ResourceBool.class);
					assertTrue(!!!res.getDataValue());
					return true;
				}
			});
		}

		assertTrue(file != null);
		test.add("Model2", new ResourceFile(file));
		return test;
	}

	@Override
	protected ResourceInterface getResourceByName(String name, boolean out)
	{
		if (name == null)
			return null;

		if ("Model1".equals(name))
		{
			ResourceFile file = loadFile(file1);
			assertTrue(file != null);
			return file;
		}
		return null;
	}

	public static void main(String args[])
	{
		(new Test_Job_Admissiblity()).testAll();
	}
}
