package kn.uni.sen.joblibrary.tartar.convert.uppaalmodel.model;

import java.util.ArrayList;
import java.util.List;

import kn.uni.sen.joblibrary.tartar.convert.HelperText;

public class Model
{
	String globalDeclaration = "";
	String system = "";
	List<Template> templateList = new ArrayList<Template>();
	List<ConstraintModel> propertyList = new ArrayList<>();
	// List<Transition> transitionList = new ArrayList<Transition>();

	boolean hasErrorState = false;

	public void addTemplate(Template templ)
	{
		templateList.add(templ);

		if (templ.hasErrorState())
			hasErrorState = true;
	}

	public boolean hasErrorState()
	{
		return hasErrorState;
	}

	private Template getTemplateClass(String name)
	{
		if ((name == null) || (name.isEmpty()))
			return null;

		for (Template templ : templateList)
		{
			if (templ.getName().compareTo(name) == 0)
				return templ;
		}

		String[] list = system.split("\n");
		for (String s : list)
		{
			if (s.contains(name + " ") || s.contains(name + "="))
			{
				int index = s.indexOf("=");
				if (index == -1)
					continue;
				s = s.substring(index + 1).replace(" ", "");
				index = s.indexOf("(");
				if (index == -1)
					continue;
				s = s.substring(0, index);
				for (Template templ : templateList)
				{
					if (templ.getName().compareTo(s) == 0)
						return templ;
				}
			}
		}
		return null;
	}

	public TemplateModel getTemplateByName(String name)
	{
		Template templ = getTemplateClass(name);
		if (templ == null)
		{
			System.out.println("Warning: Template " + name + " was not found!");
			return null;
		}
		return new TemplateModel(templ, name);
	}

	public TemplateModel getTemplateByLocationName(String name)
	{
		int index = name.indexOf(".");
		String process = "";
		if (index >= 0)
			process = name.substring(0, index);

		// todo: failure delete
		Template templ = getTemplateByLocationName2(name);
		if (templ != null)
			return new TemplateModel(templ, process);
		return null;
	}

	private Template getTemplateByLocationName2(String name)
	{
		int index = name.indexOf(".");
		String templInst = name;
		if ((index != -1) && (index != 0))
			templInst = name.substring(0, index);

		String templName = getInstanceTemplate(templInst);
		Template templ = getTemplateClass(templName);
		if (templ != null)
			return templ;

		System.out.println("Warning: Template " + templInst + " was not found!");
		return null;
	}

	private String getInstanceTemplate(String templName)
	{
		if (system == null)
			return "";
		String sys = HelperText.deleteComment(system).replace(" ", "");
		String[] strList = sys.split("\n");
		for (String line : strList)
		{

			int index = line.indexOf(templName);
			if (index == -1)
				continue;
			if (line.startsWith("system"))
			{
				// declaration is in line with system
				return templName;
			} else if (!!!line.startsWith(templName + "="))
				continue;

			String val = line.substring(index + templName.length()).replace(" ", "");
			index = val.indexOf("=");
			int index2 = val.indexOf("(");
			if ((index == -1) || (index2 == -1))
				continue;
			val = val.substring(index + 1, index2);
			return val.replace(" ", "");
		}
		return null;
	}

	public Location getLocationByName(String name)
	{
		Template templ = getTemplateByLocationName2(name);
		if (templ == null)
			return null;
		return templ.getLocationByName(name);
	}

	public void setGlobalDeclaration(String text)
	{
		globalDeclaration = text;
		parseDeclaration(globalDeclaration);
	}

	public String getGlobalDeclaration()
	{
		return globalDeclaration;
	}

	public ModelTransition getTransitionByName(String from, String to)
	{
		for (Template templ : templateList)
			for (ModelTransition trans : templ.getTransitionList())
			{
				if (trans.getFrom().compareTo(from) != 0)
					continue;
				if (trans.getTo().compareTo(to) != 0)
					continue;
				return trans;
			}
		System.out.println("Warning: Transition from " + from + " to " + to + " was not found!");
		return null;
	}

	public void setSystem(String system)
	{
		this.system = system;
	}

	public VariableModel parseGlobalVariable(String name)
	{
		VariableModel var = null;
		int index = name.indexOf(".");
		if (index != -1)
		{
			String templName = name.substring(0, index);
			Template templ = getTemplateByLocationName2(templName);
			String name2 = name.substring(index + 1);
			if (templ != null)
				var = templ.parseVariable(name2);
			if (var != null)
				var.setTemplateName(templName);
		}
		if (var == null)
			var = VariableModel.parseVariable(name, globalDeclaration);
		return var;
	}

	public VariableModel parseVariable(String process, String origin)
	{
		VariableModel var = null;
		Template templ = getTemplateClass(process);
		if (templ != null)
			var = templ.parseVariable(origin);
		if (var == null)
			var = parseGlobalVariable(origin);
		return var;
	}

	public ConstraintModel getProperty(int i)
	{
		if (propertyList.size() <= i)
			return null;
		return propertyList.get(i);
	}

	public void addProperty(String property)
	{
		if ((property == null) || property.replace(" ", "").isEmpty())
			return;
		property = property.replace("and", " && ");
		property = property.replace(" not ", "!");
		int index = property.indexOf("]");
		if (index >= 0)
			property = property.substring(index + 1);
		index = property.indexOf("!");
		if (index >= 0)
			property = property.substring(index + 1);

		ConstraintModel inv = new ConstraintModel(0, property);
		propertyList.add(inv);
	}

	public static final String[] keywordList = new String[] { "clock", "int", "chan", "broadcast", "real", "const" };

	private String isKeyWord(String s)
	{
		if (s == null)
			return null;
		for (String key : keywordList)
			if (key.compareTo(s) == 0)
				return key;
		return null;
	}

	private void parseClockFromDecl(List<String> clockList, String decl)
	{
		String[] list = decl.split(";");
		for (String str : list)
		{
			String[] list2 = str.split(" |\n");
			String type = null;
			for (String s : list2)
			{
				String t = isKeyWord(s);
				if (t != null)
				{
					type = t;
					continue;
				}
				if (type == null)
					continue;
				if (type.compareTo("clock") == 0)
					addString(clockList, s);
			}
		}
	}

	private void addString(List<String> list, String val)
	{
		if (val == null)
			return;
		for (String s : list)
			if (val.equals(s))
				return;
		list.add(val);
	}

	public List<String> getClockListAll()
	{
		List<String> clockList = new ArrayList<>();
		String decl = HelperText.deleteComment(globalDeclaration);
		parseClockFromDecl(clockList, decl);
		for (Template templ : templateList)
		{
			for (String val : templ.getDeclarationList())
				parseClockFromDecl(clockList, val);
		}
		return clockList;
	}

	public List<Template> getTemplateList()
	{
		return templateList;
	}

	String[] typeList = new String[] { "chan", "int", "real", "clock" };
	// static String[] op = { ";", ",", ">=", "<=", "!", "=" };

	public List<VariableModel> parseVariable(String val)
	{
		boolean bConst = false;
		boolean bBroad = false;
		String type = null;
		String name = null;
		String value = null;

		boolean bVal = false;
		List<VariableModel> listVar = new ArrayList<>();
		String[] list = HelperText.splitPattern(val + ";", "; =,\n");
		for (String s : list)
		{
			if (bVal)
			{
				value = s;
				bVal = false;
				continue;
			}
			if (s.isBlank())
				continue;
			if (s.compareTo("\n") == 0)
				continue;

			if ((s.compareTo(",") == 0) || (s.compareTo(";") == 0))
			{
				if ((type == null) || (name == null))
					continue;
				VariableModel var = new VariableModel(name, type, value, bConst, bBroad);
				listVar.add(var);
				name = null;
				continue;
			}
			if (s.compareTo("=") == 0)
			{
				bVal = true;
				continue;
			}
			if (s.compareTo("broadcast") == 0)
			{
				bBroad = true;
				continue;
			}
			if (s.compareTo("const") == 0)
			{
				bConst = true;
				continue;
			}

			boolean bFound = false;
			if (type == null)
				for (String typeName : typeList)
					if (s.compareTo(typeName) == 0)
					{
						type = typeName;
						bFound = true;
						break;
					}
			if (bFound)
				continue;
			name = s;
		}
		return listVar;
	}

	List<VariableModel> variableList = new ArrayList<>();

	public void parseDeclaration(String decl)
	{
		decl = HelperText.deleteComment(decl);
		int index = decl.indexOf(";");
		while (index >= 0)
		{
			String val = decl.substring(0, index);
			List<VariableModel> list = parseVariable(val);
			for (VariableModel var : list)
				variableList.add(var);
			decl = decl.substring(index + 1);
			index = decl.indexOf(";");
		}
		// for (VariableModel var : variableList)
		// System.out.println(var.toText());
		// System.out.println(decl);
	}

	public int getMaxBound()
	{
		// todo: implement correct
		List<Template> list = getTemplateList();
		int max = 0;
		for (Template templ : list)
		{
			for (Location loc : templ.getLocationList())
			{
				for (ConstraintModel con : loc.getInvariantList())
				{
					String text = con.getLabel();
					// System.out.println(text);
					int maxC = getMaxContraint(text);
					if (max < maxC)
						max = maxC;
				}
			}
			for (ModelTransition trans : templ.getTransitionList())
			{
				ConstraintModel con = trans.getGuard();
				if (con == null)
					continue;
				String text = con.getLabel();
				// System.out.println(text);
				int maxC = getMaxContraint(text);
				if (max < maxC)
					max = maxC;
			}
		}
		return max;
	}

	int parseInteger(String str)
	{
		try
		{
			int val = Integer.parseInt(str);
			return val;
		} catch (Exception ex)
		{
			return 0;
		}
	}

	private int getMaxContraint(String text)
	{
		text = HelperText.deleteComment(text);
		String[] list = HelperText.splitPattern(text, " <=>&|!");
		int max = 0;
		for (String str : list)
		{
			if (str.isBlank())
				continue;
			int val = parseInteger(str);
			if (val == 0)
				for (VariableModel var : variableList)
				{
					if ((var.getName().compareTo(str) == 0))
					{
						if (var.getValue() != null)
							val = parseInteger(var.getValue());
						break;
					}
				}
			if (max < val)
				max = val;
		}
		return max;
	}
}
