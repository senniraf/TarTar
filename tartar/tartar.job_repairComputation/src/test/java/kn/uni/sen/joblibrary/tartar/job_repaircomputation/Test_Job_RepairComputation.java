package kn.uni.sen.joblibrary.tartar.job_repaircomputation;

import static org.junit.Assert.assertTrue;

import java.net.URL;

import kn.uni.sen.joblibrary.tartar.common.SMT2_OPTION;
import kn.uni.sen.jobscheduler.common.JobAbstractTest;
import kn.uni.sen.jobscheduler.common.JobDataTest;
import kn.uni.sen.jobscheduler.common.model.Job;
import kn.uni.sen.jobscheduler.common.model.ResourceInterface;
import kn.uni.sen.jobscheduler.common.resource.ResourceEnum;
import kn.uni.sen.jobscheduler.common.resource.ResourceFile;
import kn.uni.sen.jobscheduler.common.resource.ResourceInteger;

public class Test_Job_RepairComputation extends JobAbstractTest
{
	String fileModel = "db.xml";
	String fileTrace = null; // "db.o0-t1-y-X1trace.xml";

	String modelFileUrg = "";

	{
		fileModel = "test.xml";
		fileModel = "0db2.xml";
		//fileModel = "5bando_break_ov_120_3.xml";
		// fileModel = "Test_StateTransitionMultipleTimes.xml";
		// fileModel = "1db3.xml";
		// fileModel = "7SBR_break_uv_14_1.xml";
		// fileModel = "8FDDI_break_ov_1_2.xml";
		// fileModel = "1state.xml";
		// fileModel = "2state.xml";
		// fileModel = "3state.xml";
		// fileTrace = "3state_trace.xml";
		// fileModel = "db_mk2.xml";
		// fileTrace = "db_mk2_trace.xml";

		// fileTrace = "db.o0-t1-y-X1trace.xml";

		// fileModel = "sbr_trw0.6_good_break_bv_10_5.xml";
		// fileTrace = "sbr_trw0.6_good_break_bv_10_5_trace_1.xml";

		// fileModel = "bando_break_bv_4_3.xml";
		// fileTrace = null;

		// fileModel = "PM_all_bad.xml";
		// fileTrace = null;

		// fileModel = "fischer_bad.xml";
		// fileTrace = null;

		// fileModel = "db_mk3.xml";
		// fileTrace = "db_mk3_trace.xml";

		// fileModel = "bando.xml";
		// fileTrace = null;

		// fileModel = "mcta_FB5.xml";
		// fileTrace = null;

		// fileModel = "length_test1.xml";
		// fileModel = "length_test2.xml";
		// fileModel = "length_test10.xml";
		// fileModel = "length_test20.xml";
		// fileModel = "length_test50.xml";
		// fileModel = "length_test100.xml";
		// fileTrace = null;

		// fileModel = "pacemaker2-err1-db.xml";
		// fileTrace = "pacemaker2-err1-trace.xml";

		// fileModel = "sbr_trw.ver0.5.xml";
		// fileTrace = null; // "sbr_trw.ver0.5_trace_dep.xml";

		// fileModel = "test_msg_broad.xml";
		// fileTrace = null;// "test_parser_trace_1.xml";

		// fileModel = "csma_02_bad26.xml";
		// fileTrace = null;
	}

	boolean verbose = true;
	SMT2_OPTION option = SMT2_OPTION.UNKOWN;

	static boolean z3Check = false;

	@Override
	protected Job createJob()
	{
		return new Job_RepairComputation(this);
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
			ResourceInterface res = new ResourceEnum(SMT2_OPTION.Z3.toString());
			// ResourceEnum modeInput = new ResourceEnum(option);
			// list.addResource(modeInput);
			return res;
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
