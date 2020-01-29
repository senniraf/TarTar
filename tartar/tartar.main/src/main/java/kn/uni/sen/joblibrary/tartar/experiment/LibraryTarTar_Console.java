package kn.uni.sen.joblibrary.tartar.experiment;

import java.util.ArrayList;
import java.util.List;

import kn.uni.sen.jobscheduler.common.helper.Helper;
import kn.uni.sen.jobscheduler.common.resource.ResourceFile;
import kn.uni.sen.jobscheduler.console.Console_Library;
import kn.uni.sen.jobscheduler.experiment.Experiment_Console;
import kn.uni.sen.joblibrary.tartar.JobLibrary_TarTar;

public class LibraryTarTar_Console extends Console_Library
{
	String folder = "result";

	public LibraryTarTar_Console()
	{
		super(new JobLibrary_TarTar());
	}

	@Override
	public List<String> getExperimentList()
	{
		return getStaticExperimentList();
	}

	public static List<String> getStaticExperimentList()
	{
		List<String> expList = new ArrayList<>();
		expList.add("experiment_tartar_test");
		expList.add("experiment_db2");
		expList.add("experiment_cav2019");
		expList.add("experiment_tacas2020");
		expList.add("experiment_cav2020");
		expList.add("experiment_cav2020_ex");
		expList.add("experiment_cav2020_single");
		expList.add("experiment_crest2020");
		return expList;
	}

	public static void main(String[] args)
	{
		Console_Library cons = new LibraryTarTar_Console();
		cons.run(args);
	}

	@Override
	protected List<String> createHelp(List<String> helpList)
	{
		helpList = super.createHelp(helpList);
		helpList.add("-web --web: run tartar web server");
		return helpList;
	}

	@Override
	protected Experiment_Console createExperiment(String name, List<String> args)
	{
		ResourceFile file = new ResourceFile(name);
		file.setExtension(".xml");
		String fileName = Helper.storeUrlFile(file.getData(), folder);
		if (fileName == null)
			return null;
		args.add(0, fileName);
		return new Experiment_TarTar_Console();
	}

	public static List<String> getModelRepairList()
	{
		List<String> modelList = new ArrayList<>();
		modelList.add("cav20/0db2");
		modelList.add("cav/0db");
		return modelList;
	}

	public static List<String> getModelExperimentList()
	{
		List<String> modelList = new ArrayList<>();
		modelList.add("cav20/1repairedDB2");
		modelList.add("cav/1repairedDB");
		modelList.add("cav/2csma");
		modelList.add("cav/3elevator");
		modelList.add("cav/4viking");
		modelList.add("cav/5bando");
		modelList.add("cav/6Pacemaker");
		modelList.add("cav/7SBR");
		modelList.add("cav/8FDDI");
		return modelList;
	}
}
