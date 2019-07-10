package kn.uni.se.uppal2smt2.admissible;

import static org.junit.Assert.assertTrue;

import java.net.URL;
import org.junit.Test;

import kn.uni.sen.tartar.admissible.EquivalenceCheck;
import kn.uni.sen.tartar.admissible.ResultAdm;

public class TestEquivalenceCheck
{
	@Test
	public void checkEquivalenceCheck()
	{
		ClassLoader classLoader = getClass().getClassLoader();

		String nameFile = "3state.xml";
		String nameFile2 = "4state.xml";

		// nameFile = "db.xml";
		// nameFile2 = "db_adm.xml";

		// nameFile = "PM_all_bad.xml";
		// nameFile2 = "3state.xml";

		URL res = classLoader.getResource(nameFile);
		assertTrue(res != null);
		String file1 = TestHelper.getPath(res);

		res = classLoader.getResource(nameFile2);
		assertTrue(res != null);
		String file2 = TestHelper.getPath(res);

		// file1 = "test/PM_all_good2/PM_all_good2_break_bv_1_5_comp.xml";
		// file2 = "test/PM_all_good2/PM_all_good2_break_bv_1_5_rep.xml";

		EquivalenceCheck check = new EquivalenceCheck();
		System.out.println("Check: " + nameFile + " " + nameFile);
		ResultAdm ret = check.checkEquivalence(file1, file1, "result");
		assertTrue(ret.trace == null);
		if (ret.trace == null)
			System.out.println("Equivalent TA");

		System.out.println("Check: " + nameFile + " " + nameFile2);
		ret = check.checkEquivalence(file1, file2, "result");
		assertTrue(ret.trace != null);
		if (ret.trace != null)
			System.out.println("Different TA");
	}

	public static void main(String args[])
	{
		TestEquivalenceCheck check = new TestEquivalenceCheck();
		check.checkEquivalenceCheck();
	}
}
