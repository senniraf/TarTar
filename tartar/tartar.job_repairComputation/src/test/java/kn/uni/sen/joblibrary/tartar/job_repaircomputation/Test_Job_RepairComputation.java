package kn.uni.sen.joblibrary.tartar.job_repaircomputation;

import static org.junit.Assert.assertTrue;

import java.net.URL;

import kn.uni.sen.joblibrary.tartar.common.SMT2_OPTION;
import kn.uni.sen.jobscheduler.common.JobAbstractTest;
import kn.uni.sen.jobscheduler.common.JobDataTest;
import kn.uni.sen.jobscheduler.common.model.Job;
import kn.uni.sen.jobscheduler.common.resource.ResourceEnum;
import kn.uni.sen.jobscheduler.common.resource.ResourceFile;
import kn.uni.sen.jobscheduler.common.resource.ResourceInteger;
import kn.uni.sen.jobscheduler.common.resource.ResourceInterface;
import kn.uni.sen.jobscheduler.common.resource.ResourceList;

public class Test_Job_RepairComputation extends JobAbstractTest
{
	String fileModel = "0db2.xml";
	String fileTrace = null;

	String modelFileUrg = "";

	boolean verbose = true;
	SMT2_OPTION option = SMT2_OPTION.UNKOWN;

	static boolean z3Check = false;

	@Override
	protected Job createJob()
	{
		return new Job_RepairComputation(context.handler());
	}

	protected JobDataTest createTest(Job jobTest2, int index)
	{
		if (index > 1)
			return null;
		switch (index)
		{
		case 1:
			option = SMT2_OPTION.BOUNDARY;
			break;
		case 2:
			option = SMT2_OPTION.COMPARISON;
			break;
		case 3:
			option = SMT2_OPTION.RESET;
			break;
		case 4:
			option = SMT2_OPTION.URGENT;
			// fileModel = modelFileUrg;
			break;
		case 5:
			option = SMT2_OPTION.REFERENCE;
			break;
		default:
			return null;
		}
		fileTrace = null;
		return new JobDataTest();
	}

	@Override
	protected ResourceInterface getResourceByName(String name, boolean out)
	{
		// add inputs
		if (name.compareTo("Model") == 0)
		{
			ClassLoader classLoader = getClass().getClassLoader();
			URL res = classLoader.getResource(fileModel);
			assertTrue(res != null);
			return new ResourceFile(JobAbstractTest.getPath(res));
		} else if (name.compareTo("Trace") == 0)
		{
			if (fileTrace == null)
				return null;
			ClassLoader classLoader = getClass().getClassLoader();
			URL res = classLoader.getResource(fileTrace);
			assertTrue(res != null);
			return new ResourceFile(JobAbstractTest.getPath(res));
		} else if (name.compareTo("Verbose") == 0)
		{
			return new ResourceInteger(2);
		} else if (name.compareTo("ParameterList") == 0)
		{
			ResourceList list = new ResourceList();
			// ResourceEnum modeInput = new ResourceEnum(option);
			// list.addResource(modeInput);
			list.addResource(new ResourceEnum(SMT2_OPTION.Z3.toString()));
			return list;
		} else if (name.equals("TimeoutZ3"))
		{
			return new ResourceInteger(600);
		} else if (name.equals("RepairKind"))
		{
			return new ResourceEnum(option.toString());
		}
		return null;
	}

	public static void main(String args[])
	{
		if (args.length >= 1)
		{
			if (args[0].compareTo("-z3") == 0)
				z3Check = true;
		}
		(new Test_Job_RepairComputation()).testAll();
	}
}
