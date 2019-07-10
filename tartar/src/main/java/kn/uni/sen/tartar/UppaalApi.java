package kn.uni.sen.tartar;

import java.nio.file.Paths;
import java.util.List;

import kn.uni.sen.tartar.util.Helper;
import kn.uni.sen.tartar.util.ResourceFile;
import kn.uni.sen.tartar.util.ResourceFolder;

public class UppaalApi
{
	// need to call uppaal 4.1
	// ./bin-Linux/verifyta -o0 -t1 -y -Xdb_ db.xml
	static String pathUppaal = "/home/martin/opaal/uppaal-4.1.19/bin-Linux/";

	boolean verbose = true;
	String folder = "result";
	long timeUppaal = 0;

	public UppaalApi(boolean verbose)
	{
		this.verbose = verbose;
	}

	public UppaalApi()
	{
	}

	public void setFolder(String folder)
	{
		this.folder = folder;
	}

	public static String getPath(String val)
	{
		if (!!!ResourceFile.exists(pathUppaal))
		{
			int index = val.indexOf("/tartar");
			if (index >= 0)
			{
				String path = val.substring(0, index);
				return path + "/uppaal-4.1.19/bin-Linux/";
			}
		}
		return pathUppaal;
	}

	public static String getVersion()
	{
		pathUppaal = getPath(ResourceFile.getAbsolutePath("."));
		String text = Helper.runCommand(pathUppaal + "verifyta -v", true);
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
		Helper.runCommand(pathUppaal + "verifyta -o0 -t1 -y -X" + path + name + "_trace_ " + fileModel, true, 600);
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
}
