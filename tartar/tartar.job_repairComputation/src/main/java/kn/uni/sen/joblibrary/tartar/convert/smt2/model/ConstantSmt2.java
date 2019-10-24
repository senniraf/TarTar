package kn.uni.sen.joblibrary.tartar.convert.smt2.model;

public class ConstantSmt2 implements TextSmt2
{
	String text;

	public ConstantSmt2(String text)
	{
		this.text = text;
	}
	
	public String getTextSmt2()
	{
		return text;
	}
}
