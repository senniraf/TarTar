package kn.uni.sen.tartar.admissible;

import java.io.File;
import java.util.ArrayList;
import java.util.List;
import java.util.Stack;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.OutputKeys;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerConfigurationException;
import javax.xml.transform.TransformerException;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;

import org.w3c.dom.DOMImplementation;
import org.w3c.dom.Document;
import org.w3c.dom.DocumentType;
import org.w3c.dom.Element;
import org.xml.sax.Attributes;
import org.xml.sax.helpers.DefaultHandler;

import kn.uni.sen.tartar.util.Helper;

/**
 * Traverses an NTA from a file and clones the NTA to another file
 * 
 * @author Martin Koelbl
 */
public class CloneModel extends DefaultHandler
{
	String fileCopy;

	Document doc;
	Element eleCur;
	String text = "";
	Stack<Element> stack = new Stack<>();

	// ignore this transition, since it is an error transition
	// todo: put next line in correct file CheckAdmissibility
	boolean transIgnore = false;
	boolean stateIgnore = false;
	// list with states containing "error" in name
	List<String> errorStateList = new ArrayList<>();
	String textlocation = null;
	
	public CloneModel(String fileCopy)
	{
		this.fileCopy = fileCopy;

		DocumentBuilderFactory docFactory = DocumentBuilderFactory.newInstance();
		try
		{
			DocumentBuilder docBuilder = docFactory.newDocumentBuilder();
			doc = docBuilder.newDocument();
		} catch (ParserConfigurationException e)
		{
			e.printStackTrace();
		}
	}

	private void triggerLabel(Element ele)
	{
		String kind = ele.getAttribute("kind");
		if (kind.compareTo("assignment") == 0)
			triggerUpdate(ele);
		if ((kind.compareTo("invariant") == 0) || (kind.compareTo("guard") == 0))
			triggerConstraint(ele);
	}

	protected void triggerConstraint(Element ele)
	{
	}

	protected void triggerUpdate(Element ele)
	{
	}

	protected void triggerUrgent(Element ele)
	{
	}
	
	protected void triggerState(Element ele)
	{
	}

	protected void triggerTransition(Element ele)
	{
	}

	protected void triggerDeclaration(Element eleCur2)
	{
	}

	protected void triggerTemplate(Element eleCur2, boolean start)
	{
		//System.out.println(eleCur2.getNodeName());
	}

	protected void triggerStateName(Element eleCur2)
	{
	}

	@Override
	public void endDocument()
	{
		writeFile();
	}

	void writeFile()
	{
		TransformerFactory transformerFactory = TransformerFactory.newInstance();
		try
		{
			Transformer transformer = transformerFactory.newTransformer();
			transformer.setOutputProperty(OutputKeys.ENCODING, "UTF-8");
			transformer.setOutputProperty(OutputKeys.INDENT, "yes");

			DOMImplementation domImpl = doc.getImplementation();
			DocumentType doctype = domImpl.createDocumentType("DOCTYPE", "-//Uppaal Team//DTD Flat System 1.1//EN",
					"http://www.it.uu.se/research/group/darts/uppaal/flat-1_2.dtd");
			transformer.setOutputProperty(OutputKeys.DOCTYPE_PUBLIC, doctype.getPublicId());
			transformer.setOutputProperty(OutputKeys.DOCTYPE_SYSTEM, doctype.getSystemId());

			DOMSource source = new DOMSource(doc);
			StreamResult result = new StreamResult(new File(fileCopy));
			transformer.transform(source, result);
		} catch (TransformerConfigurationException e)
		{
			e.printStackTrace();
		} catch (TransformerException e)
		{
			e.printStackTrace();
		}
	}

	Element copyElement(String namespaceURI, String localName, String qName, Attributes atts)
	{
		// staff elements
		Element ele = doc.createElement(qName);
		// set attribute to staff element
		for (int i = 0; i < atts.getLength(); i++)
		{
			String s2 = atts.getQName(i);
			String value = atts.getValue(i);
			// Attr attrCopy = doc.createAttribute(name);
			// attrCopy.setValue(value);
			ele.setAttribute(s2, value);
		}
		return ele;
	}

	@Override
	public void startElement(String namespaceURI, String localName, String qName, Attributes atts)
	{
		text = "";
		// System.out.println(qName);
		Element ele = copyElement(namespaceURI, localName, qName, atts);

		if (qName.compareTo("location") == 0)
			textlocation = atts.getValue("id");
		else if (qName.compareTo("target") == 0)
		{
			String state = atts.getValue("ref");
			for (String s : errorStateList)
				if (s.compareTo(state) == 0)
				{
					transIgnore = true;
				}
		} else if (qName.compareTo("template") == 0)
			triggerTemplate(eleCur, true);

		if (ele == null)
			return;
		if (eleCur == null)
		{
			doc.appendChild(ele);
		} else
		{
			stack.push(eleCur);
		}
		eleCur = ele;
	}

	public void characters(char[] ch, int start, int length)
	{
		for (int i = start; i < (start + length); i++)
			text += ch[i];
	}

	@Override
	public void endElement(String namespaceURI, String localName, String qName)
	{
		if (text.startsWith("\n\t"))
			text = text.substring(2);
		if (!!!text.isEmpty())
		{
			//System.out.println(text);
			text = Helper.deleteComment(text);
			//System.out.println(text);
			if (eleCur.getLastChild() == null)
				eleCur.setTextContent(text);
			if (eleCur.getNodeName().compareTo("declaration") == 0)
				triggerDeclaration(eleCur);
			text = "";
		}

		boolean ignore = false;
		if (qName.compareTo("urgent") == 0)
		{
			triggerUrgent(eleCur);
		} else if (qName.compareTo("location") == 0)
		{
			triggerState(eleCur);
			ignore = stateIgnore;
			stateIgnore = false;
			textlocation = null;
		} else if ((textlocation != null) && (qName.compareTo("name") == 0))
		{
			triggerStateName(eleCur);
		} else if (qName.compareTo("template") == 0)
			triggerTemplate(eleCur, true);

		if (qName.compareTo("label") == 0)
			triggerLabel(eleCur);
		if (qName.compareTo("transition") == 0)
		{
			triggerTransition(eleCur);
			ignore = transIgnore;
			transIgnore = false;
		}

		Element ele = eleCur;
		if (stack.isEmpty())
		{
			eleCur = null;
			ignore = true;
		} else
		{
			eleCur = stack.pop();
		}
		if (!!!ignore)
			eleCur.appendChild(ele);
	}
}
