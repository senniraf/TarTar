package kn.uni.sen.joblibrary.tartar.job_repaircomputation;

import static org.junit.Assert.assertTrue;

import kn.uni.sen.jobscheduler.common.JobAbstractTest;
import kn.uni.sen.jobscheduler.common.model.Job;
import kn.uni.sen.jobscheduler.common.model.ResourceInterface;
import kn.uni.sen.jobscheduler.common.resource.ResourceEnum;
import kn.uni.sen.joblibrary.tartar.common.SMT2_OPTION;
import kn.uni.sen.joblibrary.tartar.convert.Job_Uppaal2Smt2;
import kn.uni.sen.jobscheduler.common.resource.ResourceFile;

public class Test_Job_Convert extends JobAbstractTest
{
	String fileModel = "0db.xml";
	String fileTrace = "0db_trace.xml";

	@Override
	protected Job createJob()
	{
		return new Job_Uppaal2Smt2(this);
	}

	@Override
	protected ResourceInterface getResourceByName(String name, boolean out)
	{
		if (name == null)
			return null;
		if (name.equals("Model"))
		{
			ResourceFile file = loadFile(fileModel);
			assertTrue(file != null);
			return file;
		} else if (name.equals("Trace"))
		{
			if (fileTrace == null)
				return null;
			ResourceFile file = loadFile(fileTrace);
			assertTrue(file != null);
			return file;
		} else if (name.equals("Parameter"))
		{
			ResourceInterface res = new ResourceEnum(SMT2_OPTION.Z3);
			res.addNext(new ResourceEnum(SMT2_OPTION.BOUNDARY));
			// list.addResource(new ResourceEnum(SMT2_OPTION.RESET));
			// list.addResource(new ResourceEnum(SMT2_OPTION.URGENT));
			// list.addResource(new ResourceEnum(SMT2_OPTION.REFERENCE));
			// list.addResource(new ResourceEnum(SMT2_OPTION.COMPARISON));

			return res;
		}
		return null;
	}

	public static void main(String args[])
	{
		(new Test_Job_Convert()).testAll();
	}
}
