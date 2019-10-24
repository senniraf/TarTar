package kn.uni.sen.joblibrary.tartar.job_repaircomputation;

public class EventLogValue
{
	String name = "";
	double value = Double.NaN;
	String unit = null;

	public EventLogValue(String name, double value, String unit)
	{
		if (name != null)
			this.name = name;
		this.value = value;
		this.unit = unit;
	}

	public EventLogValue(String text)
	{
		if (text != null)
			name = text;
	}

	public String getText()
	{
		String text = name + " ";
		if (!!!Double.isNaN(value))
			text += value;
		if (unit != null)
			text += unit;
		return text;
	}

	public double getValue()
	{
		return value;
	}
}
