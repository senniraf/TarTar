package kn.uni.sen.joblibrary.tartar.modifymodel;

import java.util.ArrayList;
import java.util.List;

import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;

import kn.uni.sen.joblibrary.tartar.convert.ParseUPPAAL;

public class ParsePropertyModel extends CloneModel
{
	public class Property
	{
		public int index;
		public String form;
		public String comment;
	}

	int propCounter = 0;
	List<Property> propList = new ArrayList<>();

	public ParsePropertyModel(String modelFile)
	{
		super("");
		ParseUPPAAL.parseFile(modelFile, this);
	}

	@Override
	protected void triggerProperty(Element ele)
	{
		Property prop = new Property();
		prop.index = ++propCounter;
		NodeList list = ele.getElementsByTagName("formula");
		for (int i = 0; i < list.getLength(); i++)
		{
			Node n = list.item(i);
			String form = n.getTextContent();
			prop.form = form;
		}
		list = ele.getElementsByTagName("comment");
		for (int i = 0; i < list.getLength(); i++)
		{
			Node n = list.item(i);
			String form = n.getTextContent();
			prop.comment = form;
		}
		propList.add(prop);
	}

	@Override
	public void endDocument()
	{
	}

	public List<Property> getPropList()
	{
		return propList;
	}
}
