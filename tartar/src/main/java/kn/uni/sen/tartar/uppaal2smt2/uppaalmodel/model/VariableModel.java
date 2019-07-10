package kn.uni.sen.tartar.uppaal2smt2.uppaalmodel.model;

import java.util.ArrayList;
import java.util.List;

import kn.uni.sen.tartar.util.Helper;

/**
 * contains a variable of a declaration or constraint in an invariant or guard
 * 
 * @author Martin Koelbl
 */
public class VariableModel implements ConstraintInterface
{
	// is a constant variable
	boolean bConst;
	boolean bBroad;
	String type;
	String name;
	String value;

	String templName;

	// counter of occurence in constraint
	// for a declaration this index is 0
	int modelIndex = 0;

	public VariableModel(String name, String type, String value, boolean bC)
	{
		this.name = name;
		this.type = type;
		this.value = value;
		bConst = bC;
	}

	public VariableModel(String name2, String type2, String value2, boolean bConst2, boolean bBroad)
	{
		this.name = name2;
		this.type = type2;
		this.value = value2;
		bConst = bConst2;
		this.bBroad = bBroad;
	}

	public String getName()
	{
		return name;
	}

	public String getType()
	{
		return type;
	}

	public String getValue()
	{
		return value;
	}

	public boolean isConstant()
	{
		return bConst;
	}

	public static String parseType(String type)
	{
		if (type.compareToIgnoreCase("int") == 0)
			return "Int";

		if (type.compareToIgnoreCase("real") == 0)
			return "Real";

		if (type.compareToIgnoreCase("clock") == 0)
			return "Clock";
		if (type.startsWith("int["))
			return "Int";
		System.out.println("Warning: type unkown: " + type);
		return null;
	}

	private static String parseValue(String type, String value)
	{
		if ((type.compareToIgnoreCase("Int") != 0) && (type.compareToIgnoreCase("Real") != 0))
			return null;
		int index = value.indexOf(";");
		if (index == -1)
		{
			// System.out.println("Warning: Unkown value: " + value);
			// return null;
			// System.out.println(value);
			return value;
		}
		value = value.substring(0, index);
		// System.out.println(value);
		return value;
	}

	public static String replaceRecursive(String str, String in, String out)
	{
		String s = str;
		str = null;
		while (str != s)
		{
			str = s;
			s = str.replace(in, out);
		}
		return s;
	}

	public static VariableModel parseVariable(String name, String declarationText)
	{
		if ((declarationText == null) || (declarationText.isEmpty()))
			return null;
		try
		{
			Integer.parseInt(name);
			// a name cannot consists only of numbers
			return null;
		} catch (Exception ex)
		{
		}

		String declarationNew = Helper.deleteComment(declarationText);

		// System.out.println(name);
		String[] declList = declarationNew.split("\n");
		for (String decl : declList)
		{
			// ignore comments
			// int index = decl.indexOf("//");
			// if (index != -1)
			// decl = decl.substring(0, index);

			String[] varList = decl.split(";");
			for (String exp : varList)
			{
				if (exp.isEmpty())
					continue;

				exp = exp.trim().replace(":=", "=").replace("=", " = ");
				String expList[] = replaceRecursive(exp, "  ", " ").split(" ");
				if (expList.length < 1)
					continue;
				int count = 0;
				boolean bconst = false;
				if (expList[0].compareTo("const") == 0)
				{
					count = 1;
					bconst = true;
				}
				if (expList.length < (2 + count))
					continue;
				// array detection
				int index = expList[1 + count].lastIndexOf("]");
				if (index >= 0)
				{
					expList[0 + count] += expList[1 + count].substring(0, index + 1);
					expList[1 + count] = expList[1 + count].substring(index + 1);
					if (expList[1 + count].replace(" ", "").isEmpty() && (expList.length > 2 + count))
					{
						expList[1 + count] = expList[2 + count];
						for (int i = 2 + count; i < expList.length - 1; i++)
							expList[i] = expList[i + 1];
						expList[expList.length - 1] = "";
					}
				}

				if (expList[1 + count].compareTo(name) != 0)
					continue;
				String type = parseType(expList[0 + count]);
				if (type == null)
					continue;
				String value = null;
				if (expList.length > 3 + count)
					value = parseValue(type, expList[3 + count]);
				VariableModel var = new VariableModel(name, type, value, bconst);
				return var;
			}
		}
		return null;
	}

	public static List<VariableModel> parseVariableList(String declarationText)
	{
		String[] typeList = new String[] { "Int", "Real", "Clock" };

		List<VariableModel> list = new ArrayList<>();
		String[] lines = declarationText.split("\n");
		for (String line : lines)
		{
			// delete comments
			int index = line.indexOf("//");
			if (index >= 0)
				line = line.substring(index);
			// parse rest;
			String[] varList = line.split(";");
			for (String var : varList)
			{
				try
				{
					boolean c = false;
					if (var.contains("const "))
						c = true;
					String t = null;
					for (String type : typeList)
					{
						if (var.contains(type.toLowerCase()))
							t = type;
					}
					if (t == null)
						continue;
					index = var.indexOf("]");
					if (index >= 0)
						index++;
					else
					{
						index = var.indexOf(t.toLowerCase());
						index += t.length();
					}
					var = var.substring(index).replace(" ", "");
					index = var.indexOf("=");
					String name = var;
					if (index >= 0)
					{
						name = var.substring(0, index);
						var = var.substring(index + 1);
						if (var.isEmpty())
							var = null;
					}
					VariableModel v = new VariableModel(name, t, var, c);
					list.add(v);
				} catch (Exception ex)
				{
				}
			}
		}
		return list;
	}

	public boolean isType(String t)
	{
		if (type == null)
			return false;
		if (type.compareTo(t) == 0)
			return true;
		return false;
	}

	@Override
	public UppaalConstraintType getConstraintType()
	{
		return UppaalConstraintType.VARIABLE;
	}

	public void setIndexConstraint(int indexCon)
	{
		modelIndex = indexCon;
	}

	public int getIndexConstraint()
	{
		return modelIndex;
	}

	public void setTemplateName(String templName)
	{
		this.templName = templName;
	}

	public String getTemplateName()
	{
		return templName;
	}

	public String toText()
	{
		String var = "";
		if (bBroad)
			var += "broadcast";
		if (bConst)
			var += "const";
		var += " " + type + " ";
		if (templName != null)
			var += templName + ".";
		var += name;
		if (value != null)
			var += "=" + value;
		return var;
	}
}
