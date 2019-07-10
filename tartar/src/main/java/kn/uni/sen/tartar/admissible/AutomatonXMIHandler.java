package kn.uni.sen.tartar.admissible;

import org.xml.sax.Attributes;
import org.xml.sax.helpers.DefaultHandler;

public class AutomatonXMIHandler extends DefaultHandler
{
	AutomatonXMI aut = null;
	String text;
	boolean isInit = false;

	public AutomatonXMIHandler(AutomatonXMI aut)
	{
		this.aut = aut;
	}

	@Override
	public void startElement(String namespaceURI, String localName, String qName, Attributes atts)
	{
		if (qName.compareTo("state") == 0)
		{
			text = "";
			isInit = true; //atts.getValue("initial") != null;
		}
		if (qName.compareTo("edge") == 0)
		{
			String from = atts.getValue("from");
			String to = atts.getValue("to");
			String label = atts.getValue("label");
			aut.addEdge(from, to, label);
		}
	}

	public void characters(char[] ch, int start, int length)
	{
		if (text != null)
		{
			for (int i = start; i < (start + length); i++)
				text += ch[i];
		}
	}

	public void endElement(String namespaceURI, String localName, String qName)
	{
		if (qName.compareTo("state") == 0)
		{
			aut.addState(text, isInit);
			text = null;
		}
	}
}
