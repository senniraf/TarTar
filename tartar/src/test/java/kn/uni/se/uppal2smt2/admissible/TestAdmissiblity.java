package kn.uni.se.uppal2smt2.admissible;

import static org.junit.Assert.assertTrue;

import java.net.URL;

import org.junit.Test;

import kn.uni.sen.tartar.admissible.CheckAdmissibility;
import kn.uni.sen.tartar.admissible.Repair;
import kn.uni.sen.tartar.smtcall.ModelSolution;
import kn.uni.sen.tartar.smtcall.Modification;

public class TestAdmissiblity
{
	@Test
	public void checkAdmissibleCheck()
	{
		TestHelper.createTestFolder();
		ClassLoader classLoader = getClass().getClassLoader();
		String nameFile = "db.xml";
		Modification cv = new Modification("", "_bv1_x4_1", "0", "-1");
		cv.setID(13, 1);

		// nameFile = "db_mk3.xml";
		// cv = new ChangedValue("", "_bv_w3_1", "0", "-1");
		// cv.setID(15, 1);

		// nameFile = "PM_all_good2.xml";
		// cv = new Modification("", "_bv_clk9_1", "0", "1000");
		// cv.setID(2, 1);

		URL res = classLoader.getResource(nameFile);
		assertTrue(res != null);
		String file1 = TestHelper.getPath(res);

		//file1 = "test/PM_all_good2/PM_all_good2_break_bv_1_5.xml";
		//cv = new Modification("", "_bv_clk9_1", "0", "-400"); //-801/2
		//cv.setID(2, 1);

		ModelSolution sol1 = new ModelSolution();
		sol1.addChange(cv);

		System.out.println("Check: " + nameFile + " " + sol1.toText());
		Repair repair = CheckAdmissibility.checkAdmissibility(file1, sol1, "result");
		assertTrue(repair != null);
		if (repair.isAdmissible())
			System.out.println("Solution admissible.");
		else
			// System.out.println("Check: " + nameFile + " " + sol2.toText());
			// ret = CheckAdmissibility.checkAdmissibility(file1, sol2);
			// assertTrue(!!!ret);
			System.out.println("Solution not admissible.");
	}

	public static void main(String args[])
	{
		TestAdmissiblity check = new TestAdmissiblity();
		check.checkAdmissibleCheck();
	}
}
