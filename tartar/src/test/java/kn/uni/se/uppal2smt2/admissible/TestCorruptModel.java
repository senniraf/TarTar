package kn.uni.se.uppal2smt2.admissible;
/*
import static org.junit.Assert.assertTrue;

import java.net.URL;


import kn.uni.sen.tartar.admissible.CorruptModel;
import kn.uni.sen.tartar.uppaal2smt2.SMT2_OPTION;*/

import org.junit.Test;

public class TestCorruptModel
{

	@Test
	public void checkCorruption()
	{
		/*
		 * TestHelper.createTestFolder(); ClassLoader classLoader =
		 * getClass().getClassLoader();
		 * 
		 * String nameFile = "3state.xml"; nameFile = "test_parser.xml";
		 * 
		 * URL res = classLoader.getResource(nameFile); assertTrue(res != null);
		 * String file1 = TestHelper.getPath(res);
		 * 
		 * // CorruptModel corrupt = new CorruptModel(); for (SMT2_OPTION option
		 * : SMT2_OPTION.ListModifier) { CorruptModel corrupt = new
		 * CorruptModel(file1); corrupt.corruptFile(null, option); }
		 */
		System.out.println("Not implemented");
	}

	public static void main(String args[])
	{
		TestCorruptModel test = new TestCorruptModel();
		test.checkCorruption();
	}
}
