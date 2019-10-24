package kn.uni.sen.joblibrary.tartar.convert;

import org.xml.sax.Attributes;
import org.xml.sax.helpers.DefaultHandler;

import kn.uni.sen.joblibrary.tartar.convert.uppaaltrace.model.Clock;
import kn.uni.sen.joblibrary.tartar.convert.uppaaltrace.model.ClockBound;
import kn.uni.sen.joblibrary.tartar.convert.uppaaltrace.model.DBM;
import kn.uni.sen.joblibrary.tartar.convert.uppaaltrace.model.Edge;
import kn.uni.sen.joblibrary.tartar.convert.uppaaltrace.model.LocationVector;
import kn.uni.sen.joblibrary.tartar.convert.uppaaltrace.model.Node;
import kn.uni.sen.joblibrary.tartar.convert.uppaaltrace.model.Process;
import kn.uni.sen.joblibrary.tartar.convert.uppaaltrace.model.Trace;
import kn.uni.sen.joblibrary.tartar.convert.uppaaltrace.model.Transition;
import kn.uni.sen.joblibrary.tartar.convert.uppaaltrace.model.Variable;
import kn.uni.sen.joblibrary.tartar.convert.uppaaltrace.model.VariableState;
import kn.uni.sen.joblibrary.tartar.convert.uppaaltrace.model.VariableVector;

class UPPAALTraceHandler extends DefaultHandler
{
	String initialNode;
	Trace trace;

	// helper variables
	DBM dbmCurrent;
	Process process;
	Edge edgeCurrent = null;
	String text = null;
	LocationVector locVec = null;
	VariableVector varVec = null;

	public UPPAALTraceHandler(Trace trace)
	{
		this.trace = trace;
	}

	@Override
	public void startElement(String namespaceURI, String localName, String qName, Attributes atts)
	{
		if (qName.compareTo("trace") == 0)
		{
			initialNode = atts.getValue("initial_node");
		} else if (qName.compareTo("edge") == 0)
		{
			String id = atts.getValue("id");
			this.edgeCurrent = new Edge(id, atts.getValue("from"), atts.getValue("to"));
			trace.addEdge(edgeCurrent);
		} else if ((qName.compareTo("update") == 0) && (edgeCurrent != null))
		{
			text = new String();
		} else if ((qName.compareTo("guard") == 0) && (edgeCurrent != null))
		{
			text = new String();
		} else if ((qName.compareTo("sync") == 0) && (edgeCurrent != null))
		{
			text = new String();
		} else if (qName.compareTo("clock") == 0)
		{
			String name = atts.getValue("name");
			String id = atts.getValue("id");
			if (id != null)
				trace.addClock(new Clock(name, id));
		} else if (qName.compareTo("variable") == 0)
		{
			String name = atts.getValue("name");
			String id = atts.getValue("id");
			if (id != null)
				trace.addVariable(new Variable(name, id));
		} else if (qName.compareTo("node") == 0)
		{
			String val = atts.getValue("id");
			String locVec = atts.getValue("location_vector");
			String varVec = atts.getValue("variable_vector");
			String val2 = atts.getValue("dbm_instance");
			if (val != null)
				trace.addNode(new Node(val, locVec, varVec, val2));
		} else if (qName.compareTo("dbm_instance") == 0)
		{
			String val = atts.getValue("id");
			if (val != null)
			{
				dbmCurrent = new DBM(val);
				trace.addDBM(dbmCurrent);
			}
		} else if (qName.compareTo("clockbound") == 0)
		{
			Clock clock1 = trace.getClockByID(atts.getValue("clock1"));
			Clock clock2 = trace.getClockByID(atts.getValue("clock2"));
			String bound = atts.getValue("bound");
			String compare = atts.getValue("comp");
			if (dbmCurrent != null)
				dbmCurrent.addClockBound(new ClockBound(clock1, clock2, bound, compare));
			else
				System.out.println("Warning: Unused clockbound was found");
		} else if (qName.compareTo("transition") == 0)
		{
			String val = atts.getValue("from");
			String val2 = atts.getValue("to");
			String edgeList = atts.getValue("edges");
			Node from = trace.getNodeByName(val);
			Node to = trace.getNodeByName(val2);
			if ((val != null) && (val2 != null))
				trace.addTransition(new Transition(from, to, edgeList, trace));
		} else if (qName.compareTo("location_vector") == 0)
		{
			String id = atts.getValue("id");
			String loc = atts.getValue("locations");
			locVec = new LocationVector(id, loc);
			trace.addLocationVector(locVec);
		} else if ((qName.compareTo("variable_vector") == 0))
		{
			String id = atts.getValue("id");
			varVec = new VariableVector(id);
			trace.addVariableVector(varVec);
		} else if ((qName.compareTo("variable_state") == 0) && (varVec != null))
		{
			String id = atts.getValue("variable");
			String val = atts.getValue("value");
			varVec.addVariableState(new VariableState(id, val));
		}else if ("process".equals(qName))
		{
			String id = atts.getValue("id");
			String name = atts.getValue("name");
			process = new Process(id, name);
			trace.addProcess(process);
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
		if (qName.compareTo("trace") == 0)
		{
			if (initialNode != null)
				trace.setInitialNode(trace.getNodeByName(initialNode));

			for (Node node : trace.getNodeList())
				node.setDBM(trace.getDbmByName(node.getDbmName()));
		} else if (qName.compareTo("dbm_instance") == 0)
		{
			dbmCurrent = null;
		} else if (qName.compareTo("edge") == 0)
		{
			edgeCurrent = null;
		} else if ((qName.compareTo("guard") == 0) && (edgeCurrent != null))
		{
			edgeCurrent.setGuard(text);
			text = null;
		} else if ((qName.compareTo("sync") == 0) && (edgeCurrent != null))
		{
			edgeCurrent.setSync(text);
			text = null;
		} else if ((qName.compareTo("update") == 0) && (edgeCurrent != null))
		{
			edgeCurrent.setUpdate(text);
			text = null;
		} else if ((qName.compareTo("variable_vector") == 0) && (varVec != null))
		{
			varVec = null;
		} else if ((qName.compareTo("location_vector") == 0) && (locVec != null))
		{
			locVec = null;
		}
	}
}
