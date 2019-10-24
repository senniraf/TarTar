package kn.uni.sen.joblibrary.tartar.convert.uppaalmodel.model;

public class TemplateModel
{
	Template templ;
	String name;

	public TemplateModel(Template templ, String name)
	{
		this.templ = templ;
		this.name = name;
	}

	public String getName()
	{
		return name;
	}

	public Template getTemplate()
	{
		return templ;
	}
}
