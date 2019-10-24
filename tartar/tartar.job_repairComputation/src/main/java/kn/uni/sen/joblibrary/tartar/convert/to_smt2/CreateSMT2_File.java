package kn.uni.sen.joblibrary.tartar.convert.to_smt2;

import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.PrintStream;

import kn.uni.sen.joblibrary.tartar.convert.smt2.model.ConstraintSmt2;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.FunctionSmt2;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.TextSmt2;

public class CreateSMT2_File implements CreateSMT2
{
	String filename;
	StringBuffer text = new StringBuffer();

	boolean lastComment = false;

	boolean noAssert = false;

	int idCount = 0;

	boolean command = false;

	public CreateSMT2_File(String filename, boolean command)
	{
		this.command = command;
		this.filename = filename;
	}

	private void check()
	{
		if (lastComment)
		{
			text.append("\n");
			lastComment = false;
		}
	}

	@Override
	public void addComment(int level, String comment)
	{
		lastComment = true;
		text.append("; " + comment);
	}

	@Override
	public void addOption(String opt, String val)
	{
		check();
		text.append("(" + opt);
		if (val != null)
			text.append(val);
		text.append(")\n");
	}

	@Override
	public int startCommand(String cmd)
	{
		if (!!!command)
			return 0;
		check();
		text.append("(" + cmd);
		return idCount;
	}

	@Override
	public void addCommandParameter(String par)
	{
		if (!!!command)
			return;
		check();
		text.append(" " + par);
	}

	@Override
	public void endCommand(int id)
	{
		if (!!!command)
			return;
		check();
		if (id != idCount - 1)
		{
			System.out.println("Error: wrong command ended.");
			return;
		}
		text.append(")\n");
	}

	@Override
	public void createVariable(String name, String type)
	{
		check();
		text.append("declare-const " + name + " " + type + "\n");
	}

	@Override
	public void createFunction(String name, String type, ConstraintSmt2 con)
	{
		check();
		text.append("declare-fun " + name + " " + type + "\n");
		noAssert = true;
		addFormula(con);
		noAssert = false;
	}

	@Override
	public void addFormula(ConstraintSmt2 con)
	{
		check();
		if (!!!noAssert)
			text.append("(assert ");
		text.append(createFormula(con));
		if (!!!noAssert)
			text.append(")\n");
	}

	private String createFormula(TextSmt2 constraint)
	{
		if (!!!(constraint instanceof ConstraintSmt2))
		{
			return constraint.getTextSmt2();
		}

		ConstraintSmt2 con = (ConstraintSmt2) constraint;
		String text = "(" + con.getOperator();
		for (int i = 0; i < con.getConSize(); i++)
		{
			text += " " + createFormula(con.getCon(i));
		}
		text += ")";
		return text;
	}

	@Override
	public void finish()
	{
		try (PrintStream out = new PrintStream(new FileOutputStream(filename)))
		{
			out.print(text);
		} catch (FileNotFoundException e)
		{
			e.printStackTrace();
		}
	}

	@Override
	public void addNewLine()
	{
		text.append("\n");
	}

	@Override
	public void addFunction(FunctionSmt2 func)
	{
		check();
		boolean noAssert2 = noAssert;
		if (!!!noAssert)
			text.append("(assert ");
		noAssert = true;
		text.append("(" + func.getName() + "\n");
		text.append("(");
		for (int i = 0; i < func.getParameterSize(); i++)
		{
			if (i != 0)
				text.append(" ");
			text.append(createFormula(func.getParameter(i)));
		}
		text.append(")\n");
		text.append(createFormula(func.getBody()));

		noAssert = noAssert2;
		if (!!!noAssert)
			text.append(")\n");
	}
}
