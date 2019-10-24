package kn.uni.sen.joblibrary.tartar.common.util;

import java.io.BufferedReader;
import java.io.File;
import java.io.InputStreamReader;
import java.util.concurrent.TimeUnit;

public class CommandLine
{
	public static boolean resultB = false;

	public static String run(String cmd, boolean bText, long timeout_seconds)
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

	public static String run(String cmd, boolean bText)
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

	public static String run(String cmd, String folderPath, boolean bText)
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

}
