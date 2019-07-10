package kn.uni.sen.tartar;

import static org.junit.Assert.assertTrue;

import java.net.URL;
import java.util.LinkedList;
import java.util.List;

import org.junit.Test;

import kn.uni.se.uppal2smt2.admissible.TestHelper;
import kn.uni.sen.tartar.MainDiagnostic;
import kn.uni.sen.tartar.admissible.Repair;
import kn.uni.sen.tartar.uppaal2smt2.SMT2_OPTION;

public class MainDiagnosticTest
{
	String fileModel = "db.xml";
	String fileTrace = "db.o0-t1-y-X1trace.xml";

	boolean verbose = true;
	// String fileModel = "example/sbr_trw.ver0.7_statespate.xml";
	// String fileTrace = "example/sbrv0.7.o0-t1-y-X1trace1.xml";

	// String fileModel = "example/PM_all.xml";
	// String fileTrace = "example/PM.o0-t1-y-X1trace1.xml";

	// String fileModel = "example/dbWithConst.xml";
	// String fileTrace = "example/dbWithCons.trace.xml";

	static boolean z3Check = false;

	/*
	 * public String getNameFile() { int index = fileTrace.lastIndexOf(".xml");
	 * if (index == -1) return fileTrace; return fileTrace.substring(0, index);
	 * }
	 */

	public List<String> getTestInputParameters()
	{
		fileModel = "0db.xml";
		fileTrace = null;
		// fileModel = "3state.xml";
		// fileTrace = "3state_trace.xml";
		// fileModel = "db_mk2.xml";
		// fileTrace = "db_mk2_trace.xml";

		// fileModel = "db.xml";
		// fileTrace = "db.o0-t1-y-X1trace.xml";
		
		//fileModel = "sbr_trw0.6_good_break_bv_10_5.xml";
		//fileTrace = "sbr_trw0.6_good_break_bv_10_5_trace_1.xml";

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

		ClassLoader classLoader = getClass().getClassLoader();

		URL res = classLoader.getResource(fileModel);
		assertTrue(res != null);
		String modelPath = TestHelper.getPath(res);
		System.out.println(res.toString());

		String tracePath = null;
		if (fileTrace != null)
		{
			res = classLoader.getResource(fileTrace);
			assertTrue(res != null);
			tracePath = TestHelper.getPath(res);
		}

		List<String> list = new LinkedList<>();
		list.add("-c2");
		list.add(modelPath);
		if ((fileTrace != null) && !!!tracePath.isEmpty())
		{
			list.add("-t");
			list.add(tracePath);
		}
		return list;
	}

	// @Test
	public void testDBM()
	{
		// { "-dbm", "-c2", fileTrace, fileModel, fileDestiny };
		List<String> list = getTestInputParameters();
		list.add(0, "-dbm");
		if (z3Check)
			list.add(0, "-z3");

		MainDiagnostic.main((String[]) list.toArray(new String[list.size()]));
	}

	// @Test
	public void testInvariant()
	{
		List<String> list = getTestInputParameters();
		if (z3Check)
			list.add(0, "-z3");
		MainDiagnostic.main((String[]) list.toArray(new String[list.size()]));
	}

	@Test
	public void testBoundary()
	{
		// { "-b", "-c2", fileTrace, fileModel, fileDestiny };
		List<String> list = getTestInputParameters();
		list.add(0, "-" + SMT2_OPTION.getName(SMT2_OPTION.BOUNDARY));
		if (z3Check)
			list.add(0, "-z3");
		MainDiagnostic diagnostic = new MainDiagnostic();
		diagnostic.runDiagnostic((String[]) list.toArray(new String[list.size()]));
		if (verbose)
		{
			List<Repair> ret = diagnostic.getRepairList();
			System.out.println("");
			for (Repair r : ret)
				System.out.println(r.getModificationText());
			if (ret.isEmpty())
				System.out.println("No repair was found.");
		}
	}

	// @Test
	public void testElimination()
	{
		// { "-e", "-c2", fileTrace, fileModel, fileDestiny };
		List<String> list = getTestInputParameters();
		list.add(0, "-qe");
		if (z3Check)
			list.add(0, "-z3");
		MainDiagnostic.main((String[]) list.toArray(new String[list.size()]));
	}

	// @Test
	public void testReference()
	{
		List<String> list = getTestInputParameters();
		list.add(0, "-" + SMT2_OPTION.getName(SMT2_OPTION.REFERENCE));
		if (z3Check)
			list.add(0, "-z3");
		MainDiagnostic.main((String[]) list.toArray(new String[list.size()]));
	}

	// @Test
	public void testReset()
	{
		List<String> list = getTestInputParameters();
		list.add(0, "-" + SMT2_OPTION.getName(SMT2_OPTION.RESET));
		if (z3Check)
			list.add(0, "-z3");
		MainDiagnostic.main((String[]) list.toArray(new String[list.size()]));
	}

	// @Test
	public void testComparison()
	{
		List<String> list = getTestInputParameters();
		list.add(0, "-" + SMT2_OPTION.getName(SMT2_OPTION.COMPARISON));
		if (z3Check)
			list.add(0, "-z3");
		MainDiagnostic.main((String[]) list.toArray(new String[list.size()]));
	}

	// @Test
	public void testUrgent()
	{
		List<String> list = getTestInputParameters();
		list.add(0, "-" + SMT2_OPTION.getName(SMT2_OPTION.URGENT));
		if (z3Check)
			list.add(0, "-z3");
		MainDiagnostic.main((String[]) list.toArray(new String[list.size()]));
	}

	public void testAll()
	{
		// testDBM();
		// testInvariant();
		// testElimination();

		testBoundary();
		// testComparison();
		// testReference();
		// testReset();
		// testUrgent();
	}

	public static void main(String args[])
	{
		if (args.length >= 1)
		{
			if (args[0].compareTo("-z3") == 0)
				z3Check = true;
		}
		(new MainDiagnosticTest()).testAll();
	}
}
