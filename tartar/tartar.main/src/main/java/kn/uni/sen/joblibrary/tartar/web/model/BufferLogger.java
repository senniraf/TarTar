package kn.uni.sen.joblibrary.tartar.web.model;

import java.util.concurrent.ArrayBlockingQueue;

import kn.uni.sen.jobscheduler.common.impl.EventLoggerAbstract;
import kn.uni.sen.jobscheduler.common.impl.JobEventStatus;
import kn.uni.sen.jobscheduler.common.model.EventHandler;
import kn.uni.sen.jobscheduler.common.model.JobEvent;

public class BufferLogger extends EventLoggerAbstract
{
	ArrayBlockingQueue<JobEvent> eventList;

	public BufferLogger(int bufSize)
	{
		super(2);
		eventList = new ArrayBlockingQueue<>(bufSize);
		//addTest();
	}

	protected void addTest()
	{
		eventList.add(new JobEventStatus(JobEvent.ERROR, "Error"));
		eventList.add(new JobEventStatus(JobEvent.WARNING, "Warning"));
		eventList.add(new JobEventStatus(JobEvent.INFO, "Info"));
		eventList.add(new JobEventStatus(JobEvent.DEBUG, "Debug"));
	}

	@Override
	public boolean logEvent(EventHandler handler, JobEvent event)
	{
		if (!!!isEvent(event))
			return false;

		eventList.add(event);
		return true;
	}

	public JobEvent getNextEvent()
	{
		if (eventList.isEmpty())
		{
			//addTest();
			return null;
		}
		return eventList.remove();
	}
}
