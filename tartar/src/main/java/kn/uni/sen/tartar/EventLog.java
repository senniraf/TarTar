package kn.uni.sen.tartar;

import java.util.ArrayList;
import java.util.List;

public class EventLog
{
	String event;
	long timeMS = System.currentTimeMillis();
	List<EventLogValue> valueList = new ArrayList<>();

	EventLog(String event)
	{
		this.event = event;
	}

	public void addEventValue(String name, double value, String unit)
	{
		valueList.add(new EventLogValue(name, value, unit));
	}
	
	public void addEventValue(String text)
	{
		valueList.add(new EventLogValue(text));
	}

	public long getTime()
	{
		return timeMS;
	}

	public String getText()
	{
		return event + getValueText();
	}

	public String getValueText()
	{
		String text = "";
		for (EventLogValue val : valueList)
			text += val.getText() + " ";
		return text;
	}
}
