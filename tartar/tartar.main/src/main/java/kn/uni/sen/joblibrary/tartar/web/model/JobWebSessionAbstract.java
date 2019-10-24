package kn.uni.sen.joblibrary.tartar.web.model;

public class JobWebSessionAbstract implements JobWebSession
{
	Integer id;

	public JobWebSessionAbstract(Integer id)
	{
		this.id = id;
	}

	@Override
	public Integer getId()
	{
		return id;
	}

	@Override
	public void setId(Integer id)
	{
		this.id = id;
	}
}
