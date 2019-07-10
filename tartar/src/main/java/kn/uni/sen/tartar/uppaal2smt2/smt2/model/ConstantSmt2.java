package kn.uni.sen.tartar.uppaal2smt2.smt2.model;

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
