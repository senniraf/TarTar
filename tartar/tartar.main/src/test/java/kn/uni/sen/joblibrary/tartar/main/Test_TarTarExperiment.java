package kn.uni.sen.joblibrary.tartar.main;

import kn.uni.sen.joblibrary.tartar.experiment.Experiment_TarTar_Console;
import kn.uni.sen.jobscheduler.common.JobAbstractTest;
import kn.uni.sen.jobscheduler.common.resource.ResourceFile;

public class Test_TarTarExperiment
{
	public static void main(String[] args)
	{
		ResourceFile expFile = JobAbstractTest.loadFile("experiment_db2.xml");
		if ((expFile == null) || (expFile.getData() == null))
		{
			System.out.println("Missing experiment file");
			return;
		}
		String[] expList = new String[] { expFile.getData() };
		Experiment_TarTar_Console.main(expList);
	}
}
