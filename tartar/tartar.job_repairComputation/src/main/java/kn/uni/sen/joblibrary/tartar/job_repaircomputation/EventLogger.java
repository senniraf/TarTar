package kn.uni.sen.joblibrary.tartar.job_repaircomputation;

import java.util.ArrayList;
import java.util.List;
import java.util.Timer;
import java.util.TimerTask;

import kn.uni.sen.jobscheduler.common.model.RunContext;
import kn.uni.sen.joblibrary.tartar.common.CheckAdmissibility;
import kn.uni.sen.joblibrary.tartar.common.util.CommandLine;
import kn.uni.sen.jobscheduler.common.model.JobEvent;
import kn.uni.sen.jobscheduler.common.resource.ResourceFile;

public class EventLogger
{
	boolean verbose = false;
	List<EventLog> eventList = new ArrayList<>();
	long startTime = System.currentTimeMillis();
	long timeLast = startTime;
	Timer timer = new Timer("check", true);

	float maxMemoryUsed;
	float maxMemoryEvent;
	RunContext context;

	class TimerWork extends TimerTask
	{
		@Override
		public void run()
		{
			checkMemory();
			if (adm != null)
			{
				long val = CommandLine.getMem();
				adm.checkMem(val);
			}
		}
	}

	public EventLogger(boolean verbose)
	{
		this(verbose, null);
	}

	CheckAdmissibility adm;

	public EventLogger(boolean verbose, RunContext context)
	{
		this.verbose = verbose;
		this.context = context;
		timer.schedule(new TimerWork(), 0, 100);
		// HelperConsole.runCommand("./resmem ", null, true);
	}
	
	public void setAdm(CheckAdmissibility adm)
	{
		this.adm = adm;
	}

	public void end()
	{
		timer.cancel();
	}

	public EventLog logEvent(String event)
	{
		EventLog ev = new EventLog(event);
		logEvent(ev);
		return ev;
	}

	public void logValue(String event, String name, double value, String unit)
	{
		EventLog ev = new EventLog(event);
		ev.addEventValue(name, value, unit);
		logEvent(ev);
	}

	private String getSingleEvent(EventLog ev)
	{
		long dif = ev.getTime() - startTime;
		long difLast = ev.getTime() - timeLast;
		timeLast = ev.getTime();
		// if (verbose)
		// getMemory();
		return (((float) dif) / 1000) + "s   " + (((float) difLast) / 1000) + "s, " + ev.getText();
	}

	public String getEventText()
	{
		String text = "";
		timeLast = startTime;
		for (EventLog ev : eventList)
			text += getSingleEvent(ev) + "\n";
		return text;
	}

	Runtime instance = Runtime.getRuntime();

	void checkMemory()
	{
		System.gc();
		float val = instance.totalMemory() - instance.freeMemory();
		if (val > maxMemoryUsed)
			maxMemoryUsed = val;
		if (val > maxMemoryEvent)
			maxMemoryEvent = val;
	}

	void getMemory()
	{
		float mb = 1024 * 1024;
		context.logEventStatus(JobEvent.INFO, "Memory Max: " + (maxMemoryUsed / mb) + "MB");
		context.logEventStatus(JobEvent.INFO, "Memory Event: " + (maxMemoryEvent / mb) + "MB");
	}

	public void save2File(String fileName)
	{
		ResourceFile.writeText2File(fileName, getEventText());
	}

	public void logEvent(EventLog ev)
	{
		eventList.add(ev);
		maxMemoryEvent = 0;
		if (verbose)
			context.logEventStatus(JobEvent.INFO, getSingleEvent(ev));
	}
}
