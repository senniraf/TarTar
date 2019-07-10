package kn.uni.sen.tartar.uppaal2smt2;

import org.xml.sax.Attributes;
import org.xml.sax.helpers.DefaultHandler;

import kn.uni.sen.tartar.uppaal2smt2.uppaalmodel.model.Location;
import kn.uni.sen.tartar.uppaal2smt2.uppaalmodel.model.Model;
import kn.uni.sen.tartar.uppaal2smt2.uppaalmodel.model.ModelTransition;
import kn.uni.sen.tartar.uppaal2smt2.uppaalmodel.model.Template;

class UPPAALModelHandler extends DefaultHandler
{
	Model model;

	// helper variables
	Template template;
	Location location;
	ModelTransition transition;
	String label;
	String kind; // of label inside of transition
	String system;
	String property;

	int idCounter = 0;

	public UPPAALModelHandler(Model m)
	{
		this.model = m;
	}

	@Override
	public void startElement(String namespaceURI, String localName, String qName, Attributes atts)
	{
		if (qName.compareTo("template") == 0)
		{
			template = new Template(model);
		} else if (qName.compareTo("location") == 0)
		{
			String val = atts.getValue("id");
			location = new Location(val);
			location.setIDModel(++idCounter);
		} else if ((qName.compareTo("urgent") == 0) && (location != null))
		{
			location.setUrgent(true);
		} else if ((qName.compareTo("committed") == 0) && (location != null))
		{
			location.setUrgent(true);
		} else if (qName.compareTo("transition") == 0)
		{
			transition = new ModelTransition();
			transition.setIDModel(++idCounter);
		} else if ((qName.compareTo("source") == 0) && (transition != null))
		{
			String val = atts.getValue("ref");
			transition.setFrom(val);
		} else if ((qName.compareTo("target") == 0) && (transition != null))
		{
			String val = atts.getValue("ref");
			transition.setTo(val);
		} else if ((qName.compareTo("label") == 0) && (transition != null))
		{
			label = "";
			this.kind = atts.getValue("kind");
		} else if ((qName.compareTo("name") == 0) && (location != null))
		{
			label = "";
		} else if ((qName.compareTo("label") == 0) && (location != null))
		{
			label = "";
			this.kind = atts.getValue("kind");
		} else if ((template != null) && (qName.compareTo("name") == 0))
		{
			label = "";
		} else if ((template != null) && (qName.compareTo("declaration") == 0))
		{
			label = "";
		} else if ((qName.compareTo("declaration") == 0))
		{
			label = "";
		} else if ((qName.compareTo("parameter") == 0))
		{
			label = "";
		} else if ((qName.compareTo("system") == 0))
		{
			system = "";
		} else if ((qName.compareTo("init") == 0))
		{
			String val = atts.getValue("ref");
			template.setInit(val);
		} else if ((qName.compareTo("formula") == 0))
		{
			property = "";
		}
	}

	public void characters(char[] ch, int start, int length)
	{
		if (label != null)
		{
			for (int i = start; i < (start + length); i++)
				label += ch[i];
		}
		if (system != null)
		{
			for (int i = start; i < (start + length); i++)
				system += ch[i];
		}
		if (property != null)
		{
			for (int i = start; i < (start + length); i++)
				property += ch[i];
		}
	}

	public void endElement(String namespaceURI, String localName, String qName)
	{
		if (qName.compareTo("template") == 0)
		{
			model.addTemplate(template);
			template = null;
		} else if (qName.compareTo("location") == 0)
		{
			template.addLocation(location);
			location = null;
		} else if (qName.compareTo("transition") == 0)
		{
			template.addTransition(transition);
			transition = null;
		} else if ((transition != null) && (qName.compareTo("label") == 0))
		{
			transition.addLabel(kind, label);
			kind = null;
			label = null;
		} else if ((location != null) && (qName.compareTo("name") == 0))
		{
			location.addName(label);
			label = null;
		} else if ((location != null) && (qName.compareTo("label") == 0))
		{
			location.addLabel(kind, label);
			kind = null;
			label = null;
		} else if ((template != null) && (qName.compareTo("name") == 0))
		{
			template.addName(label);
			label = null;
		} else if ((template != null) && (qName.compareTo("declaration") == 0))
		{
			template.addDeclaration(label);
			label = null;
		} else if ((template != null) && (qName.compareTo("parameter") == 0))
		{
			template.setParameterList(label);
			label = null;
		} else if (qName.compareTo("declaration") == 0)
		{
			model.setGlobalDeclaration(label);
			label = null;
		} else if ((qName.compareTo("system") == 0))
		{
			model.setSystem(system);
			system = null;
		} else if (qName.compareTo("formula") == 0)
		{
			model.addProperty(property);
			property = null;
		}
	}
}
