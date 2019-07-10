package kn.uni.sen.tartar.uppaal2smt2;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;

import javax.xml.parsers.ParserConfigurationException;
import javax.xml.parsers.SAXParser;
import javax.xml.parsers.SAXParserFactory;

import org.xml.sax.SAXException;
import org.xml.sax.helpers.DefaultHandler;

import kn.uni.sen.tartar.admissible.AutomatonXMI;
import kn.uni.sen.tartar.admissible.AutomatonXMIHandler;
import kn.uni.sen.tartar.uppaal2smt2.uppaalmodel.model.Model;
import kn.uni.sen.tartar.uppaal2smt2.uppaaltrace.model.Trace;

/**
 * Parses a uppaal model trace or file in xml syntax
 * 
 * @author Martin Koelbl
 */
public class ParseUPPAAL<T>
{
	T t;

	public T parseFile(String file, T t)
	{
		this.t = t;

		DefaultHandler handler = null;
		if (t.getClass() == Trace.class)
			handler = new UPPAALTraceHandler((Trace) t);
		else if (t.getClass() == Model.class)
			handler = new UPPAALModelHandler((Model) t);
		else if (t.getClass() == AutomatonXMI.class)
			handler = new AutomatonXMIHandler((AutomatonXMI) t);
		if (!!!parseFile(file, handler))
			return null;
		return this.t;
	}

	static public boolean parseFile(String file, DefaultHandler handler)
	{
		SAXParserFactory factory = SAXParserFactory.newInstance();
		SAXParser saxParser;
		try
		{
			saxParser = factory.newSAXParser();
			saxParser.parse(new File(file), handler);
			return true;
		} catch (ParserConfigurationException e)
		{
			e.printStackTrace();
		} catch (SAXException e)
		{
			e.printStackTrace();
		} catch (FileNotFoundException e)
		{
			System.out.println("Error: File " + file + " not found.");
		} catch (IOException e)
		{
			e.printStackTrace();
		}
		return false;
	}
}
