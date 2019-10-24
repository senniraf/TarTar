package kn.uni.sen.joblibrary.tartar.web.form;

public class OptionsForm
{
	private String propertyName;
	private String optionName;
	private int timeZ3 = 120;

	public String getPropertyName()
	{
		return propertyName;
	}

	public void setPropertyName(String property)
	{
		this.propertyName = property;
	}

	public String getOptionName()
	{
		return optionName;
	}

	public void setOptionName(String name)
	{
		this.optionName = name;
	}

	public int getTimeZ3()
	{
		return timeZ3;
	}

	public void getTimeZ3(int time)
	{
		this.timeZ3 = time;
	}
}
