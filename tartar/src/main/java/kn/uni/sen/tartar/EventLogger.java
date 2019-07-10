package kn.uni.sen.tartar;

import java.util.ArrayList;
import java.util.List;
import java.util.Timer;
import java.util.TimerTask;

import kn.uni.sen.tartar.util.Helper;

public class EventLogger
{
	boolean verbose = false;
	List<EventLog> eventList = new ArrayList<>();
	long startTime = System.currentTimeMillis();
	long timeLast = startTime;
	Timer timer = new Timer();

	float maxMemoryUsed;
	float maxMemoryEvent;

	class TimerWork extends TimerTask
	{
		@Override
		public void run()
		{
			checkMemory();
		}
	}

	public EventLogger(boolean verbose)
	{
		this.verbose = verbose;
		//timer.schedule(new TimerWork(), 0, 100);
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
		System.out.println("Memory Max: " + (maxMemoryUsed / mb) + "MB");
		System.out.println("Memory Event: " + (maxMemoryEvent / mb) + "MB");
	}

	public void save2File(String fileName)
	{
		Helper.writeText2File(fileName, getEventText());
	}

	public void logEvent(EventLog ev)
	{
		eventList.add(ev);
		maxMemoryEvent = 0;
		if (verbose)
			System.out.println(getSingleEvent(ev));
	}
}
