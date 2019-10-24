package kn.uni.sen.joblibrary.tartar.convert.uppaalmodel.model;

import java.util.ArrayList;
import java.util.List;

import org.mariuszgromada.math.mxparser.Expression;
import org.mariuszgromada.math.mxparser.parsertokens.Token;

import kn.uni.sen.joblibrary.tartar.convert.HelperText;

/**
 * contains a constraint of an invariant or guard
 * 
 * @author Martin Koelbl
 */
public class ConstraintModel implements ConstraintInterface
{
	int id;
	String label;
	Model model;

	List<ConstraintInterface> conList = new ArrayList<>();

	// index counter for occurence of a variable or clock
	int indexCon = 0;

	public ConstraintModel(int id, String label)
	{
		this.id = id;
		this.label = label;
	}

	public String getLabel()
	{
		return label;
	}

	public String getOperator()
	{
		return label;
	}

	public int getID()
	{
		return id;
	}

	@Override
	public UppaalConstraintType getConstraintType()
	{
		return UppaalConstraintType.CONSTRAINT;
	}

	protected void addConstraint(ConstraintInterface con)
	{
		conList.add(con);
	}

	public List<ConstraintInterface> getConstraintList()
	{
		return conList;
	}


	public ConstraintInterface parseConstraint(TemplateModel templ)
	{
		return parseConstraint(templ, label);
	}

	class Operator
	{
		int paraCount;
		String name;

		public Operator(int c, String name)
		{
			paraCount = c;
			this.name = name;
		}
	}

	Operator[] OperatorList = { new Operator(2, ":="), new Operator(1, "!"), new Operator(1, "++"),
			new Operator(1, "--"), new Operator(2, "-"), new Operator(2, "+"), new Operator(2, "*"),
			new Operator(2, "/"), new Operator(2, "^"), new Operator(2, "=="), new Operator(2, "<="),
			new Operator(2, ">="), new Operator(2, "<"), new Operator(2, ">"), new Operator(2, "&&"),
			new Operator(2, "||"), };

	int token_counter = 0;
	int parse_depth = 0;

	private ConstraintInterface parseToken(ConstraintInterface child, TemplateModel templ, List<Token> tokenList)
	{
		ConstraintInterface current = child;
		boolean braket = false;
		this.parse_depth++;
		for (; token_counter < tokenList.size();)
		{
			Token tok = tokenList.get(token_counter);
			token_counter++;
			if (tok.tokenStr.compareTo("(") == 0)
			{
				current = parseToken(null, templ, tokenList);
				this.parse_depth--;
				// increment closing braket
				token_counter++;
				braket = true;
				return current;
			}
			if (tok.tokenStr.compareTo(")") == 0)
				return current;
			// parse operator
			for (Operator op : OperatorList)
			{
				if (op.name.compareTo(tok.tokenStr) != 0)
					continue;
				// operator found
				int op_count = op.paraCount;
				ConstraintModel cm = new ConstraintModel(0, op.name);
				int i = 0;
				if (current != null)
				{
					cm.addConstraint(current);
					i++;
				}
				current = cm;
				// wait for operator arguments
				for (; i < op_count; i++)
				{
					int depth = parse_depth;
					ConstraintInterface cm_child = parseToken(null, templ, tokenList);
					if (depth != parse_depth)
						return null;
					if (cm_child == null)
						return null;
					cm.addConstraint(cm_child);
				}
				parse_depth--;
				return cm;
			}

			// check if element is variable
			if (templ != null)
				current = templ.getTemplate().getModel().parseVariable(templ.getName(), tok.tokenStr);
			else
				current = model.parseVariable(null, tok.tokenStr);
			// current = templ.getTemplate().parseVariable(tok.tokenStr);
			if (current != null)
			{
				break;
			}
			// System.out.println(tok.tokenStr);
			current = new ConstantModel(tok.tokenStr);
			break;
		}
		// current formula satisfies syntax, in depth of another formula
		// if (parse_depth > 1)
		// {
		// parse_depth--;
		// return current;
		// }

		// current formula satisfies syntax, but is not yet finished
		for (; token_counter < tokenList.size();)
		{
			Token tok = tokenList.get(token_counter);
			if (tok.tokenStr.compareTo(")") == 0)
			{
				// braket can only be closed in the depth of baket opening
				if (braket)
					token_counter++;
				parse_depth--;
				return current;
			}
			current = parseToken(current, templ, tokenList);
		}
		parse_depth--;
		return current;
	}

	public static String getConstraintText(ConstraintInterface con)
	{
		if (con == null)
			return "null";
		String text = "";
		if (con.getClass() == ConstraintModel.class)
		{
			ConstraintModel cm = (ConstraintModel) con;
			text = "(" + cm.getOperator() + " ";
			for (ConstraintInterface child : cm.getConstraintList())
			{
				text += getConstraintText(child) + " ";
			}
			return text + ")";
		}
		if (con.getClass() == VariableModel.class)
		{
			VariableModel vm = (VariableModel) con;
			return vm.getName();
		}
		if (con.getClass() == ConstantModel.class)
		{
			ConstantModel cm = (ConstantModel) con;
			return cm.getValue();
		}
		return "?";
	}

	protected ConstraintInterface parseConstraint(TemplateModel templ, String text)
	{
		text = HelperText.deleteComment(text);
	
		// ugly work around: create a correct parser!
		ConstraintInterface cm = null;
		if (text.contains("&&"))
		{
			String[] list = text.split("&&");
			for (String sub : list)
			{
				ConstraintInterface part = parseConstraint(templ, sub);
				if (cm != null)
				{
					ConstraintModel model = new ConstraintModel(0, "&&");
					model.addConstraint(cm);
					model.addConstraint(part);
					cm = model;
				} else
					cm = part;
			}
		} else
		// if (text.compareTo("x > (k-1) && id == pid") == 0)
		// {
		// int t = 0;
		// t++;
		// }
		{
			Expression eh = new Expression(text);
			List<Token> tokensList = eh.getCopyOfInitialTokens();
			token_counter = 0;
			parse_depth = 0;
			cm = parseToken(null, templ, tokensList);
		}
		// System.out.println(getConstraintText(cm));

		if (parse_depth != 0)
		{
			System.out.println("Warning: Formula parser ended with wrong depth!");
			System.out.println(text);
			return null;
		}
		return cm;
	}

	public List<ConstraintModel> parseUpdate(TemplateModel templ)
	{
		String text = HelperText.deleteComment(label).replace("\n", "").replace(" ", "");
		List<ConstraintModel> opList = new ArrayList<>();
		String[] split = text.split(",");
		for (String con : split)
		{
			int index = con.indexOf(":=");
			if (index < 0)
				continue;
			String name = con.substring(0, index);
			ConstraintModel operation = new ConstraintModel(id, ":=");

			if (templ == null)
			{
				System.out.println("Warning: Missing Template.");
				continue;
			}

			VariableModel v = templ.getTemplate().parseVariable(name);
			if (v == null)
			{
				System.out.println("Warning: Update variable was not found.");
				continue;
			}
			v.setIndexConstraint(++indexCon);

			operation.addConstraint(v);

			String cText = con.substring(index + 2);
			ConstraintInterface c = parseConstraint(templ, cText);
			if (c == null)
			{
				System.out.println("Warning: Update constraint was not parsed.");
				continue;
			}
			operation.addConstraint(c);
		}
		return opList;
	}

	public void setModel(Model model)
	{
		this.model = model;
	}
}
