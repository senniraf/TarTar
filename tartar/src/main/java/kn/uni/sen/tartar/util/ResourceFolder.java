package kn.uni.sen.tartar.util;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

/**
 * Resource saves a folder from filesytem
 */
public class ResourceFolder
{
	public static boolean createFolder(String folder)
	{
		if ((folder == null) || folder.isEmpty())
			return false;
		File jobGraphFolder = new File(folder);
		if (!!!jobGraphFolder.exists())
			jobGraphFolder.mkdirs();
		if (!!!jobGraphFolder.exists())
			return false;
		return true;
	}

	public static List<String> getFiles(String path, String end)
	{
		String endText = end;
		if ((end == null) || (end.compareTo("*") == 0))
			endText = null;

		List<String> textFiles = new ArrayList<String>();
		File dir = new File(path);
		for (File file : dir.listFiles())
		{
			if ((endText == null) || file.getName().endsWith(endText))
			{
				textFiles.add(file.getName());
			}
		}
		return textFiles;
	}
}
