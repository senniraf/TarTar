package kn.uni.sen.tartar.uppaal2smt2.smt2.model;

import java.util.ArrayList;
import java.util.List;

public class FunctionSmt2 implements TextSmt2
{
	String name;
	String bodyOperator;

	List<VariableSmt2> varList = new ArrayList<>();
	ConstraintSmt2 body;

	public FunctionSmt2(String op, String bodyOperator)
	{
		name = op;
		body = new ConstraintSmt2(bodyOperator);
	}

	public void addParameter(VariableSmt2 var)
	{
		varList.add(var);
	}

	public int getParameterSize()
	{
		return varList.size();
	}

	public VariableSmt2 getParameter(int i)
	{
		return varList.get(i);
	}

	public void addBody(ConstraintSmt2 con)
	{
		body.addCon(con);
	}

	public ConstraintSmt2 getBody()
	{
		return body;
	}

	@Override
	public String getTextSmt2()
	{
		String text = "(" + name + " ";
		return text;
	}

	public String getName()
	{
		return name;
	}
}
