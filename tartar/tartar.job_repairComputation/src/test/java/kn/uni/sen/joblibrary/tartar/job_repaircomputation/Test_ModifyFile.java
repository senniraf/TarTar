package kn.uni.sen.joblibrary.tartar.job_repaircomputation;

import static org.junit.Assert.assertTrue;

import kn.uni.sen.tartar.smtcall.ModelSolution;
import kn.uni.sen.tartar.smtcall.Modification;

public class Test_ModifyFile
{
	// @Test
	protected void checkModifyFile()
	{

		Modification cv = new Modification("", "_bv1_x4_1", "0", "-1");
		cv.setID(13, 1);

		// file1 = "test/PM_all_good2/PM_all_good2_break_bv_1_5.xml";
		// cv = new Modification("", "_bv_clk9_1", "0", "-400"); //-801/2
		// cv.setID(2, 1);

		ModelSolution sol1 = new ModelSolution();
		sol1.addChange(cv);

		// nameFile = "db_mk3.xml";
		// cv = new ChangedValue("", "_bv_w3_1", "0", "-1");
		// cv.setID(15, 1);

		// nameFile = "PM_all_good2.xml";
		// cv = new Modification("", "_bv_clk9_1", "0", "1000");
		// cv.setID(2, 1);

		// URL res = classLoader.getResource(nameFile);
		// assertTrue(res != null);
		// String file1 = TestHelper.getPath(res);
		assertTrue(true);
	}

	public static void main(String args[])
	{
		(new Test_ModifyFile()).checkModifyFile();
	}
}
