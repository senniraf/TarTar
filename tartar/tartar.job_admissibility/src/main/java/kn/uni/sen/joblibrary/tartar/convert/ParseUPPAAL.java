package kn.uni.sen.joblibrary.tartar.convert;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;

import javax.xml.parsers.ParserConfigurationException;
import javax.xml.parsers.SAXParser;
import javax.xml.parsers.SAXParserFactory;

import org.xml.sax.SAXException;
import org.xml.sax.helpers.DefaultHandler;

/**
 * Parses a uppaal model trace or file in xml syntax
 * 
 * @author Martin Koelbl
 */
public abstract class ParseUPPAAL<T>
{
	protected abstract DefaultHandler createHandler(T t);

	public T parseFile(String file, T t)
	{
		DefaultHandler handler = createHandler(t);
		if (!!!parseFile(file, handler))
			return null;
		return t;
	}

	static public boolean parseFile(String file, DefaultHandler handler)
	{
		if (file == null)
			return false;

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
