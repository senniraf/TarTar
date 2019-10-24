package kn.uni.sen.joblibrary.tartar.convert;

import java.util.ArrayList;
import java.util.List;
import java.util.TimerTask;

/**
 * Some helper functions
 * 
 * @author Martin Koelbl
 */
public class HelperText
{
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

	public static final String ANSI_RED = "\u001B[31m";
	public static final String ANSI_GREEN = "\u001B[32m";
	public static final String ANSI_YELLOW = "\u001B[33m";
	public static final String ANSI_RESET = "\u001B[0m";

	public static void testColorMessage()
	{
		HelperText.outputMessage("Error: todo");
		HelperText.outputMessage("Warning: todo");
		HelperText.outputMessage("Good: todo");
		HelperText.outputMessage("todo");
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
