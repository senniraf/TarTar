package kn.uni.sen.tartar.util;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.PrintWriter;
import java.nio.file.Files;
import java.nio.file.NoSuchFileException;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;
import java.util.TimerTask;
import java.util.concurrent.TimeUnit;

/**
 * Some helper functions
 * 
 * @author Martin Koelbl
 */
public class Helper
{
	public static boolean checkExists(String filePath)
	{
		File f = new File(filePath);
		return f.exists() && !!!f.isDirectory();
	}

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

	public static boolean copyFile(String original, String fileDestiny)
	{
		// Files.copy(original, file, StandardCopyOption.REPLACE_EXISTING);
		InputStream inStream = null;
		OutputStream outStream = null;
		try
		{
			inStream = new FileInputStream(new File(original));
			outStream = new FileOutputStream(new File(fileDestiny));

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

	public static boolean appendText2File(String file, String text)
	{
		if (text == null)
			return true;
		try (FileWriter fw = new FileWriter(file, true);
				BufferedWriter bw = new BufferedWriter(fw);
				PrintWriter out = new PrintWriter(bw))
		{
			out.println(text);
			return true;
		} catch (IOException e)
		{
		}
		return false;
	}

	public static String parseFile(String fileName)
	{
		try
		{
			return new String(Files.readAllBytes(Paths.get(fileName)));
		} catch (IOException e)
		{
			e.printStackTrace();
			return null;
		}
	}

	public static boolean writeText2File(String fileDestiny, String text)
	{
		// Files.copy(original, file, StandardCopyOption.REPLACE_EXISTING);
		OutputStream outStream = null;
		try
		{
			outStream = new FileOutputStream(new File(fileDestiny));
			outStream.write(text.getBytes(), 0, text.length());
			outStream.close();
			return true;
		} catch (IOException e)
		{
			e.printStackTrace();
		}
		return false;
	}

	public static void deleteFile(String filePath)
	{
		try
		{
			Files.deleteIfExists(Paths.get(filePath));
		} catch (NoSuchFileException x)
		{
		} catch (IOException x)
		{
			// File permission problems are caught here.
			System.err.println(x);
		}
	}

	public static boolean resultB = false;

	static class TaskMem extends TimerTask
	{
		public long maxMem = 0;
		public Runtime r;

		public TaskMem(Runtime runtime)
		{
			r = runtime;
			maxMem = 0;
		}

		@Override
		public void run()
		{
			long mem = r.totalMemory() - r.freeMemory();
			if (maxMem < mem)
				maxMem = mem;
		}

		public static TaskMem createTask(Runtime runtime)
		{
			return new TaskMem(runtime);
		}
	}

	public static String runCommand(String cmd, boolean bText, long timeout_seconds)
	{
		try
		{
			String line;
			Process p = Runtime.getRuntime().exec(cmd);
			BufferedReader input = new BufferedReader(new InputStreamReader(p.getInputStream()));
			StringBuffer buffer = new StringBuffer();

			resultB = false;
			resultB = p.waitFor(timeout_seconds, TimeUnit.SECONDS);
			if (bText)
				while ((line = input.readLine()) != null)
				{
					// System.out.println(line);
					buffer.append(line);
				}
			input.close();
			return buffer.toString();
		} catch (Exception err)
		{
			err.printStackTrace();
		}
		return null;
	}

	public static String runCommand(String cmd, boolean bText)
	{
		try
		{
			String line;
			Process p = Runtime.getRuntime().exec(cmd);
			BufferedReader input = new BufferedReader(new InputStreamReader(p.getInputStream()));
			StringBuffer buffer = new StringBuffer();
			result = p.waitFor();
			if (bText)
				while ((line = input.readLine()) != null)
				{
					// System.out.println(line);
					buffer.append(line);
				}
			input.close();
			return buffer.toString();
		} catch (Exception err)
		{
			err.printStackTrace();
		}
		return null;
	}

	// todo: solve ugly return value
	public static int result = -3;

	public static String runCommand(String cmd, String folderPath, boolean bText)
	{
		result = -2;
		try
		{
			String line;
			Runtime r = Runtime.getRuntime();
			// Process p = r.exec(cmdList);
			File folder = new File(folderPath);

			// TaskMem task = TaskMem.createTask(Runtime.getRuntime());
			// Timer timer = new Timer();
			// timer.schedule(task, 100);

			Process p = r.exec(cmd, null, folder);
			BufferedReader input = new BufferedReader(new InputStreamReader(p.getInputStream()));
			StringBuffer buffer = new StringBuffer();
			boolean res = p.waitFor(3600, TimeUnit.SECONDS);
			if (!!!res)
				return "";
			result = p.exitValue();
			// timer.cancel();
			// task.run();
			// double mem2 = task.maxMem / 1024.0 / 1024.0;
			// we only check the current process but not the called one by exec
			// System.out.println("Memory: " + mem2);
			if (bText)
				while ((line = input.readLine()) != null)
				{
					buffer.append(line);
					buffer.append("\n");
				}
			input.close();
			return buffer.toString();
		} catch (Exception err)
		{
			err.printStackTrace();
		}
		return null;
	}

	public static String textDeleteUntil(String text, String pattern)
	{
		int index = text.indexOf(pattern);
		if (index < 0)
			return text;
		index += pattern.length();
		return text.substring(index);
	}

	public static String textDeleteFrom(String text, String pattern)
	{
		int index = text.indexOf(pattern);
		if (index < 0)
			return text;
		return text.substring(0, index);
	}

	public static int countOccurrences(String z3Code, String word)
	{
		String[] list = z3Code.split(word);
		return list.length - 1;
	}

	public static final String ANSI_RED = "\u001B[31m";
	public static final String ANSI_GREEN = "\u001B[32m";
	public static final String ANSI_YELLOW = "\u001B[33m";
	public static final String ANSI_RESET = "\u001B[0m";

	public static void testColorMessage()
	{
		Helper.outputMessage("Error: todo");
		Helper.outputMessage("Warning: todo");
		Helper.outputMessage("Good: todo");
		Helper.outputMessage("todo");
	}

	public static void outputMessage(String text)
	{
		// todo: this does not work yet
		String color = null;
		if (text.startsWith("Error:"))
			color = ANSI_RED;
		if (text.startsWith("Warning:"))
			color = ANSI_YELLOW;
		if (text.startsWith("Good:"))
			color = ANSI_GREEN;

		if (color == null)
			System.out.println(text);
		else
			System.out.println(color + text + ANSI_RESET);
	}

	/** Function delete any comments in an text */
	public static String deleteComment(String text)
	{
		String[] split = text.split("\n");
		text = "";
		boolean gC = false;
		for (String line : split)
		{
			String tLine = line;
			boolean mod = true;
			while (mod)
			{
				mod = false;
				int indexGO = tLine.indexOf("/*");
				int indexGC = tLine.indexOf("*/");
				int indexLine = tLine.indexOf("//");
				if (gC)
					// global comment is closed by */
					if (indexGC <= 0)
						tLine = "";
					else
					{
						gC = false;
						mod = true;
						tLine = tLine.substring(indexGC);
						continue;
					}
				else if ((indexLine >= 0) && ((indexGO < 0) || (indexLine <= indexGO)))
				{
					// next comment is line comment
					tLine = tLine.substring(0, indexLine);
				} else if ((indexGO >= 0) && (indexGC >= 0))
				{
					// first comment is global comment and also closed in this
					// line
					tLine = tLine.substring(0, indexGO) + tLine.substring(indexGC + 2);
				} else if (indexGO >= 0)
				{
					// first comment is global comment and not closed in this
					// line
					tLine = line.substring(0, indexGO);
					gC = true;
				}
			}
			if (!!!tLine.isEmpty())
			{
				if (!!!text.isEmpty())
					text += "\n";
				text += tLine;
			}
		}
		return text;
	}

	public static int nextCharIndex(String str, String pat)
	{
		for (int j = 0; j < str.length(); j++)
		{
			for (int i = 0; i < pat.length(); i++)
			{
				if (str.charAt(j) == pat.charAt(i))
					return j;
			}
		}
		return -1;
	}

	public static String[] splitPattern(String val, String pat)
	{
		List<String> list = new ArrayList<>();
		while (!!!val.isEmpty())
		{
			int index = nextCharIndex(val, pat);
			if (index < 0)
			{
				list.add(val);
				break;
			}

			String sub = val.substring(0, index);
			list.add(sub);
			val = val.substring(index);
			sub = val.substring(0, 1);
			list.add(sub);
			val = val.substring(1);
		}
		return list.toArray(new String[] {});
	}

}
