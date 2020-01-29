package kn.uni.sen.joblibrary.tartar.common.util;

import java.io.BufferedReader;
import java.io.File;
import java.io.InputStreamReader;
import java.util.concurrent.TimeUnit;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import kn.uni.sen.jobscheduler.common.helper.HelperConsole;

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

	// public static long PID = 0;
	static Pattern pat = Pattern.compile("total kB[ ]*\\d+[ ]*(\\d+)[ ]*");

	// public static synchronized void setPID(long pid)
	// {
	// PID = pid;
	// }

	public static synchronized long getMem()
	{
		String pidText = HelperConsole.runCommand("pidof opaal2lts-mc", null, true);
		int p = 0;
		try
		{
			pidText = pidText.replace("\n", "");
			p = Integer.parseInt(pidText);
		} catch (Exception ex)
		{
			return -1;
		}

		String ret = HelperConsole.runCommand("pmap " + p, null, true);
		Matcher mat = pat.matcher(ret);
		if (!!!mat.find())
			return -1;
		String val2 = mat.group(1);
		if (val2 == null)
			return -1;

		try
		{
			return Integer.parseInt(val2) / 1024;
		} catch (Exception e)
		{
		}
		return -1;
	}

	// public static synchronized long getMemUppaal()
	// {
	// String pidText = HelperConsole.runCommand("pidof verifyta", null, true);
	// int p = 0;
	// try
	// {
	// pidText = pidText.replace("\n", "");
	// p = Integer.parseInt(pidText);
	// } catch (Exception ex)
	// {
	// return -1;
	// }
	// // if (PID == 0)
	// // return -1;
	// String ret = HelperConsole.runCommand("pmap " + p, null, true);
	// Matcher mat = pat.matcher(ret);
	// if (!!!mat.find())
	// return -1;
	// String val2 = mat.group(1);
	// if (val2 == null)
	// return -1;
	//
	// try
	// {
	// return Integer.parseInt(val2) / 1024;
	// } catch (Exception e)
	// {
	// }
	// return -1;
	// }

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
			// setPID(p.pid());
			BufferedReader input = new BufferedReader(new InputStreamReader(p.getInputStream()));
			StringBuffer buffer = new StringBuffer();
			boolean res = p.waitFor(3600, TimeUnit.SECONDS);
			// setPID(0);
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
