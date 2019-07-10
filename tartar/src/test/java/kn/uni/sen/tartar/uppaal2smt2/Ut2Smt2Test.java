package kn.uni.sen.tartar.uppaal2smt2;

import static org.junit.Assert.assertTrue;

import java.net.URL;
import java.util.LinkedList;
import java.util.List;

import org.junit.Test;

import kn.uni.se.uppal2smt2.admissible.TestHelper;
import kn.uni.sen.tartar.uppaal2smt2.Ut2Smt2;
import kn.uni.sen.tartar.util.ResourceFile;

public class Ut2Smt2Test
{
	String fileTrace = ""; // "example_ut/o0-t1-y-X1.trace.xml";
	String fileModel = "";// "example_ut/o0-t1-y-X1.db.xml";

	static boolean z3Check = false;

	// String fileTrace = "example_ut/pacemaker2-err1-trace.xml";
	// String fileModel = "example_ut/pacemaker2-err1-db.xml";

	// String fileTrace = "db_trace1.xml";
	// String fileModel = "example_uppaal/db.xml";

	public Ut2Smt2Test()
	{
		fileTrace = getFilePath("o0-t1-y-X1.trace.xml");
		fileModel = getFilePath("o0-t1-y-X1.db.xml");
	}

	private String getFilePath(String nameFile)
	{
		ClassLoader classLoader = getClass().getClassLoader();
		URL res = classLoader.getResource(nameFile);
		assertTrue(res != null);
		return TestHelper.getPath(res);
	}

	public String getNameFile()
	{
		String file = ResourceFile.getFilenameOnly(fileTrace);
		file = "test/" + file;
		return file;
	}

	public List<String> getTestInputParameters(String fileDestiny)
	{
		List<String> list = new LinkedList<>();
		list.add("-c2");
		list.add(fileTrace);
		list.add(fileModel);
		if (fileDestiny != null)
			list.add(fileDestiny);
		return list;
	}

	@Test
	public void testDBM()
	{
		// { "-dbm", "-c2", fileTrace, fileModel, fileDestiny };
		List<String> list = getTestInputParameters(getNameFile() + ".smt2");
		list.add(0, "-dbm");
		if (z3Check)
			list.add(0, "-z3");

		Ut2Smt2.main((String[]) list.toArray(new String[list.size()]));
	}

	@Test
	public void testInvariant()
	{
		List<String> list = getTestInputParameters(getNameFile() + ".smt2");
		if (z3Check)
			list.add(0, "-z3");
		Ut2Smt2.main((String[]) list.toArray(new String[list.size()]));
	}

	@Test
	public void testBoundary()
	{
		// { "-b", "-c2", fileTrace, fileModel, fileDestiny };
		List<String> list = getTestInputParameters(getNameFile() + ".smt2");
		list.add(0, "-" + SMT2_OPTION.boundary_name);
		if (z3Check)
			list.add(0, "-z3");
		Ut2Smt2.main((String[]) list.toArray(new String[list.size()]));
	}

	@Test
	public void testElimination()
	{
		// { "-e", "-c2", fileTrace, fileModel, fileDestiny };
		List<String> list = getTestInputParameters(getNameFile() + ".smt2");
		list.add(0, "-" + SMT2_OPTION.qe_name);
		if (z3Check)
			list.add(0, "-z3");
		Ut2Smt2.main((String[]) list.toArray(new String[list.size()]));
	}

	@Test
	public void testReference()
	{
		List<String> list = getTestInputParameters(getNameFile() + ".smt2");
		list.add(0, "-" + SMT2_OPTION.reference_name);
		if (z3Check)
			list.add(0, "-z3");
		Ut2Smt2.main((String[]) list.toArray(new String[list.size()]));
	}

	@Test
	public void testReset()
	{
		List<String> list = getTestInputParameters(getNameFile() + ".smt2");
		list.add(0, "-" + SMT2_OPTION.reset_name);
		if (z3Check)
			list.add(0, "-z3");
		Ut2Smt2.main((String[]) list.toArray(new String[list.size()]));
	}

	@Test
	public void testComparison()
	{
		List<String> list = getTestInputParameters(getNameFile() + ".smt2");
		list.add(0, "-" + SMT2_OPTION.operator_name);
		if (z3Check)
			list.add(0, "-z3");
		Ut2Smt2.main((String[]) list.toArray(new String[list.size()]));
	}

	@Test
	public void testUrgent()
	{
		List<String> list = getTestInputParameters(getNameFile() + ".smt2");
		list.add(0, "-" + SMT2_OPTION.urgent_name);
		if (z3Check)
			list.add(0, "-z3");
		Ut2Smt2.main((String[]) list.toArray(new String[list.size()]));
	}

	public void testAll()
	{
		testDBM();
		testInvariant();
		testBoundary();
		testElimination();
		testReference();
		testReset();
		testComparison();
		testUrgent();
	}

	public static void main(String args[])
	{
		if (args.length >= 1)
		{
			if (args[0].compareTo("-z3") == 0)
				z3Check = true;
		}
		(new Ut2Smt2Test()).testAll();
	}
}
