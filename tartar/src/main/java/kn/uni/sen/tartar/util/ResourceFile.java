package kn.uni.sen.tartar.util;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.text.DateFormat;
import java.text.SimpleDateFormat;
import java.util.Date;

/**
 * Resource give possibility to read and write a file.
 */
public class ResourceFile
{
	/**
	 * add date and time to foldername
	 * 
	 * @param folder
	 *            where file shall be created
	 * @param fileName
	 *            fileName that should be used
	 * @return filename with date and time
	 */
	public static String getUniqueFolderDateTime(String folder)
	{
		// "ExampleFile'16Nov11_11:11:11'.txt"
		// the part between '' is the part automatically created

		DateFormat dateFormat = new SimpleDateFormat("yyyy-MM-dd_HH-mm-ss");
		Date date = new Date(System.currentTimeMillis());
		String unique = folder.concat("_" + dateFormat.format(date));
		return getUniqueFolder(unique);
	}

	public static String getUniqueFolder(String folder)
	{
		// todo: check if folder is unique else append number
		return folder;
	}

	/**
	 * add date and time to filename
	 * 
	 * @param folder
	 *            where file shall be created
	 * @param fileName
	 *            fileName that should be used
	 * @return filename with date and time
	 */
	public static String getFileWithDateTime(String folder, String fileName)
	{
		// TODO: create a fileName with actual date and time
		// "ExampleFile'16Nov11_11:11:11'.txt"
		// the part between '' is the part automatically created
		return fileName;
	}

	/**
	 * if file already exists incremental number is added
	 * 
	 * @param folder
	 *            where file shall be created
	 * @param fileName
	 *            fileName that should be used
	 * @return unique filename
	 */
	public static String getUniqueFile(String folder, String fileName)
	{
		DateFormat dateFormat = new SimpleDateFormat("yyyy_MM_dd_HH_mm_ss");
		Date date = new Date();

		String file = getFilenameOnly(fileName);
		String type = getFileType(fileName);
		String com = folder + "/" + file + "_"+dateFormat.format(date) + "." + type;
		// TODO: create a unique fileName by checking if the file already exists
		// "ExampleFile'_2'.txt"
		// the part between '' is the part automatically created
		return com;
	}

	public static String getFilename(String fileUrl)
	{
		int index = fileUrl.lastIndexOf("/");
		if (index == -1)
			return fileUrl;
		return fileUrl.substring(index + 1);
	}

	/**
	 * @param fileUrl
	 * @return file name without folder and extension
	 */
	public static String getFilenameOnly(String fileUrl)
	{
		String name = getFilename(fileUrl);
		int index = name.lastIndexOf(".");
		if (index == -1)
			return name;
		return name.substring(0, index);
	}

	public static String getFileType(String fileUrl)
	{
		String name = getFilename(fileUrl);
		int index = name.lastIndexOf(".");
		if (index == -1)
			return "";
		return name.substring(index + 1);
	}

	// parses the resource according to the specifications
	/*
	 * public static Resource ParseResource(String qName, Attributes attributes)
	 * { System.out.println("Parse ResourceFile"); ResourceFile res = new
	 * ResourceFile(); return res; }
	 */
	public static boolean copyFile(String original, String file)
	{
		// Files.copy(original, file, StandardCopyOption.REPLACE_EXISTING);
		InputStream inStream = null;
		OutputStream outStream = null;
		try
		{
			inStream = new FileInputStream(new File(original));
			outStream = new FileOutputStream(new File(file));

			byte[] buffer = new byte[1024];

			int length;
			// copy the file content in bytes
			while ((length = inStream.read(buffer)) > 0)
			{
				outStream.write(buffer, 0, length);
			}
			inStream.close();
			outStream.close();
			return true;
		} catch (IOException e)
		{
			e.printStackTrace();
		}
		return false;
	}

	public static String readContent(String file)
	{
		BufferedReader reader;
		String line = null;
		StringBuilder stringBuilder = new StringBuilder();
		String ls = System.getProperty("line.separator");
		try
		{
			reader = new BufferedReader(new FileReader(file));
			while ((line = reader.readLine()) != null)
			{
				stringBuilder.append(line);
				stringBuilder.append(ls);
			}
			reader.close();
			return stringBuilder.toString();
		} catch (FileNotFoundException e)
		{
			e.printStackTrace();
		} catch (IOException e)
		{
			e.printStackTrace();
		}
		return "";
	}

	public static void deleteFile(String tmpFile)
	{
		File file = new File(tmpFile);
		if (file.exists())
			file.delete();
	}

	public static boolean exists(String path)
	{
		File file = new File(path);
		return file.exists();
	}

	public static String getAbsolutePath(String filePath)
	{
		Path path = Paths.get(filePath);
		return path.toAbsolutePath().toString();
	}
}
