package kn.uni.sen.joblibrary.tartar.common.uppaal;

import java.nio.file.Paths;
import java.util.List;

import kn.uni.sen.joblibrary.tartar.common.util.CommandLine;
import kn.uni.sen.jobscheduler.common.model.RunContext;
import kn.uni.sen.jobscheduler.common.resource.ResourceFile;
import kn.uni.sen.jobscheduler.common.resource.ResourceFolder;

public class UppaalApi
{
	// need to call uppaal 4.1
	// ./bin-Linux/verifyta -o0 -t1 -y -Xdb_ db.xml
	static String pathUppaal = null;

	boolean verbose = true;
	String folder = "result";
	long timeUppaal = 0;

	RunContext jobContext = null;

	public UppaalApi(RunContext context)
	{
		jobContext = context;
		this.folder = context.getFolderText();
	}

	public UppaalApi(RunContext context, boolean verbose)
	{
		jobContext = context;
		this.folder = context.getFolderText();
		this.verbose = verbose;
	}

	public static String getUppaalPath(String val)
	{
		if (!!!ResourceFile.exists(pathUppaal))
		{
			String parentFolder = ResourceFolder.getParentFolder(val);
			if (parentFolder != null)
			{
				String test = parentFolder + "/uppaal-4.1.23/bin-Linux/";
				if (ResourceFile.exists(test))
					pathUppaal = test;
				else
					getUppaalPath(parentFolder);
			}
		}
		return pathUppaal;
	}

	public static String getVersion()
	{
		String cur = ResourceFolder.getCurrentPath();
		pathUppaal = getUppaalPath(cur);
		// String relative = new File(cur).toURI().relativize(new
		// File(pathUppaal).toURI()).getPath();
		String cal = pathUppaal + "verifyta -v";
		String text = CommandLine.run(cal, true);
		int index = -1;
		if (text != null)
			index = text.indexOf("UPPAAL");
		if (index == -1)
			return "";
		int end = text.indexOf(",", index);
		return text.substring(index, end);
	}

	public static boolean checkVersion()
	{
		String version = getVersion();
		String[] list = version.split(" ");
		for (String string : list)
			if (string.startsWith("4.1"))
				return true;
		if (list.length > 2)
		{
			System.out.println("Error: Wrong version of Uppaal's verifyta: " + version + "\nNeed: UPPAAL 4.1.*");
		} else if (!!!pathUppaal.isEmpty())
		{
			pathUppaal = "";
		} else
		{
			System.out.println("Error: Missing Uppaal's verifyta");
		}

		return false;
	}

	public String createCounterexample(String fileModel)
	{
		timeUppaal = 0;
		if ((fileModel == null) || !!!checkVersion())
			return null;

		String name = ResourceFile.getFilenameOnly(fileModel);
		String path = Paths.get(".").toAbsolutePath().normalize().toString() + "/" + folder + "/";
		ResourceFolder.createFolder(path);
		// System.out.println(pathUppaal + "verifyta -o0 -t1 -y -X" + path +
		// name + "_trace_ " + fileModel);
		long time = System.currentTimeMillis();
		CommandLine.run(pathUppaal + "verifyta -o0 -t1 -y -X" + path + name + "_trace_ " + fileModel, true, 60);
		timeUppaal = System.currentTimeMillis() - time;
		// System.out.println("Time:" + timeUppaal);

		List<String> list = ResourceFolder.getFiles(path, ".xml");
		for (String file : list)
			if (file.contains(name + "_trace_"))
				return path + file;
		if (verbose)
			System.out.println("Error: No trace file found - Property may be satisfied");
		return "";
	}

	public long getUppaalTime()
	{
		return timeUppaal;
	}

	public void setFolder(String folder)
	{
		this.folder = folder;
	}
}
