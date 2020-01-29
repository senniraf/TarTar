package kn.uni.sen.joblibrary.tartar.job_tracecausality;

public class ThreeState<T>
{
	String text = null;
	boolean error;
	T value;

	public ThreeState(String errorText)
	{
		error = true;
		text= errorText;
	}

	public ThreeState(T val)
	{
		this.value = val;
	}

	public T getValue()
	{
		return value;
	}
	
	public boolean isError()
	{
		return error;
	}

	String getText()
	{
		return text;
	}
}
