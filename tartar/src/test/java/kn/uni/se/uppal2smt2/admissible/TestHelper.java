package kn.uni.se.uppal2smt2.admissible;

import java.io.UnsupportedEncodingException;
import java.net.URL;
import java.net.URLDecoder;

import kn.uni.sen.tartar.util.ResourceFile;
import kn.uni.sen.tartar.util.ResourceFolder;

public class TestHelper
{
	static String folder = "result";

	public static void createTestFolder()
	{
		if (!!!ResourceFile.exists(folder))
			ResourceFolder.createFolder(folder);
	}

	
	/**
	 * @param fileUrl
	 *            of file
	 * @return filepath as encoded as UTF-8
	 */
	public static String getPath(URL fileUrl)
	{
		if (fileUrl == null)
			return "";
		// --- from here to next comment it is just a test on how to encode
		// not very nice but it works
		// maven creates another encoding as eclipse java
		String val = fileUrl.getPath();
		int index = val.indexOf('%');
		// --- end not nice test

		if (index == -1)
			return fileUrl.getPath();

		try
		{
			return URLDecoder.decode(fileUrl.getPath(), "UTF-8");
		} catch (UnsupportedEncodingException e1)
		{
			e1.printStackTrace();
		}
		return null;
	}
}
