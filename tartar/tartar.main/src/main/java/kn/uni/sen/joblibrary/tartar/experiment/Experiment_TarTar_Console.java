package kn.uni.sen.joblibrary.tartar.experiment;

import java.net.URL;
import java.util.ArrayList;
import java.util.List;

import kn.uni.sen.joblibrary.tartar.common.TarTarConfiguration;
import kn.uni.sen.jobscheduler.common.resource.Helper;
import kn.uni.sen.jobscheduler.common.resource.ResourceFile;
import kn.uni.sen.jobscheduler.common.resource.ResourceFolder;
import kn.uni.sen.jobscheduler.experiment.Experiment_Console;
import kn.uni.sen.jobscheduler.experiment.Job_Experiment;

public class Experiment_TarTar_Console extends Experiment_Console
{
	public Experiment_TarTar_Console(String[] args)
	{
		super(args);
		System.out.println("Java Version: " + Helper.getJavaVersion());
		// experiment file by args
		// ResourceFile file = new ResourceFile(args[0]);
		// if (file.getExtension() == null)
		// file.setExtension(".xml");

		String filePath = storeFile(args[0]);
		// get QuantUM library path
		// String[] list = new String[] { "-Library", lib, "-Experiment",
		// filePath, "-Pre", pack + " \\\n" };
		// this.Args = list;

		List<String> list = new ArrayList<>();
		list.add(Job_Experiment.class.getSimpleName());
		list.add("-Library");
		list.add(getLib());
		list.add("-Experiment");
		list.add(filePath);
		//list.add("-Pre");
		//String pack = TarTarMain.class.getName();
		//list.add(pack + " \\\n");
		boolean con = false;
		for (String s : args)
			if (s.equals("-run") || s.equals("-Run"))
				con = true;
		if (con)
			list.add("-Run");

		this.runArgs = list.toArray(new String[] {});
	}

	public static void loadDynamicLibrary(String libraryName)
	{
		int val = Helper.getJavaVersion();
		System.out.println("Java Version " + val);
		String libSource = libraryName.replace(".jar", "_v" + val + ".jar");

		ClassLoader classLoader = Experiment_TarTar_Console.class.getClassLoader();
		URL urlFile = classLoader.getResource(libSource);
		if (urlFile == null)
		{
			System.out.println("Library " + libraryName + " not found. Only Java 11 and 12 are supported.");
			return;
		}
		String curLib = libraryName;
		ResourceFile.writeURL2File(urlFile, "lib/" + curLib);

		Helper.addLoadLib("./lib");
	}

	private String getLib()
	{
		String version = TarTarConfiguration.getVersion();
		String lib = "tartar.main-" + version /* + "-jar-with-dependencies" */ + ".jar";
		String libMaven = "target" + ResourceFolder.getSplitSign() + lib;
		if (ResourceFile.exists(libMaven))
			lib = libMaven;
		return lib;
	}

	static String storeFile(String nameFile)
	{
		if (ResourceFile.exists(nameFile))
			return nameFile;

		ClassLoader classLoader = Experiment_TarTar_Console.class.getClassLoader();
		URL urlFile = classLoader.getResource(nameFile);
		if (urlFile == null)
			return nameFile;
		nameFile = urlFile.getPath();
		ResourceFile file = new ResourceFile(nameFile);

		if (file.exists())
			return nameFile;

		file.setFolder("result");
		String filePath = file.getData();

		// anaPath.createFolder();
		ResourceFile.writeURL2File(urlFile, filePath);
		return filePath;
	}

	public static void main(String args[])
	{
		if (args.length == 0)
		{
			System.out.println("Give experiment file as argument.");
			return;
		}
		(new Experiment_TarTar_Console(args)).run();
	}
}
