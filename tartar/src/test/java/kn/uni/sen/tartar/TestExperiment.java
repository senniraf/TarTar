package kn.uni.sen.tartar;

import static org.junit.Assert.assertTrue;

import java.net.URL;
import java.util.ArrayList;
import java.util.List;

import kn.uni.se.uppal2smt2.admissible.TestHelper;
import kn.uni.sen.tartar.Experiment;
import kn.uni.sen.tartar.smtcall.Z3Call;

public class TestExperiment
{
	// @Test
	public void checkExperiment()
	{
		TestHelper.createTestFolder();
		ClassLoader classLoader = getClass().getClassLoader();

		List<String> list = new ArrayList<>();
		list.add("casestudy/1repairedDB.xml");
		//list.add("casestudy/2csma.xml");
		//list.add("casestudy/3elevator.xml");
		//list.add("casestudy/4viking.xml");
		//list.add("casestudy/5bando.xml");
		//list.add("casestudy/6Pacemaker.xml");
		//list.add("casestudy/7SBR.xml");
		//list.add("casestudy/8FDDI.xml");

		Z3Call.timeout = 120000; // 600 = 10 min /org: 120 sec

		for (String nameFile : list)
		{
			URL res = classLoader.getResource(nameFile);
			if (res == null)
				continue;
			assertTrue(res != null);
			String file = TestHelper.getPath(res);

			Experiment exp = new Experiment();
			exp.runExp(file);
		}
		System.out.println("End Experiment");
	}

	public static void main(String args[])
	{
		TestExperiment check = new TestExperiment();
		check.checkExperiment();
	}
}
