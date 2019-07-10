package kn.uni.sen.tartar.admissible;

import java.util.List;

import org.w3c.dom.Element;

import kn.uni.sen.tartar.smtcall.Modification;
import kn.uni.sen.tartar.uppaal2smt2.SMT2_OPTION;
import kn.uni.sen.tartar.uppaal2smt2.smt2modify.Smt2ModComparison;

public class ModifyModel extends CloneModel
{
	List<Modification> modList;

	int idCounter = 0; // counts states and transitions
	Repair repair = null; // shows modidies constraint
	Element eleUrgent = null;

	boolean bMod = false;
	boolean delErrorState = false;

	public ModifyModel(String fileCopy, List<Modification> modList, boolean delErrorState)
	{
		super(fileCopy);
		this.modList = modList;
		this.delErrorState = delErrorState;
	}

	public boolean isModified()
	{
		return bMod;
	}

	@Override
	protected void triggerConstraint(Element ele)
	{
		for (Modification changeConstraint : modList)
		{
			// counter is incremented at end of node
			if (changeConstraint.getID() != idCounter + 1)
				continue;
			// System.out.println(idCounter + 1);

			if (changeConstraint.getOption() == SMT2_OPTION.BOUNDARY)
				modifyBound(ele, changeConstraint);
			else if (changeConstraint.getOption() == SMT2_OPTION.COMPARISON)
				modifyComparison(ele, changeConstraint);
			else if (changeConstraint.getOption() == SMT2_OPTION.REFERENCE)
				modifyReference(ele, changeConstraint);
		}
	}

	protected void modifyBound(Element ele, Modification changeConstraint)
	{
		String con = ele.getTextContent();
		// int val = Integer.parseInt(changeConstraint.getValueNew());
		String val = changeConstraint.getValueNew();
		if ((val == null) || val.isEmpty())
			return;
		val = removeDivision(val);

		String conNew = con;

		if (changeConstraint.getValueNew().startsWith("-"))
		{
			conNew += "-" + val.substring(1);
		} else
		{
			conNew += "+" + val;
		}
		// System.out.println(con + " " + changeConstraint.getName());
		ele.setTextContent(conNew);
		echoModification(changeConstraint, con, conNew);
	}

	private String removeDivision(String val)
	{
		int index = val.indexOf("/");
		if (index < 0)
			return val;
		String[] list = val.split("/");
		try
		{
			double val1 = Integer.parseInt(list[0]);
			double val2 = Integer.parseInt(list[1]);
			double res = val1 / val2;
			return "" + res;
		} catch (Exception ex)
		{
			return val;
		}
	}

	protected void modifyComparison(Element ele, Modification change)
	{
		String con = ele.getTextContent();
		String op = null;
		// todo: get right new operator and replace old operator
		for (int i = 0; i < Smt2ModComparison.opList.length; i++)
		{
			int index2 = con.indexOf(Smt2ModComparison.opList[i]);
			if (index2 >= 0)
			{
				op = Smt2ModComparison.opList[i];
				break;
			}
		}

		String opNew = change.getValueNew();

		// String conNew = con.replace(change.getValueDefault(),
		// change.getValueNew());
		String conNew = con.replace(op, opNew);
		ele.setTextContent(conNew);
		echoModification(change, con, conNew);
	}

	String getVariableName(String name)
	{
		int index = name.indexOf("_", 1);
		if (index < 0)
			return "";
		name = name.substring(index + 1);
		String[] list = name.split("[0-9]_");
		if (list.length == 2)
		{
			String val1 = list[0].replaceAll("\\d*$", "");
			return val1;
		}
		return "";
	}

	protected void modifyReference(Element ele, Modification change)
	{
		String con = ele.getTextContent();
		if (change.getName() != null)
		{ // repair
			String part = change.getName().replace("_" + SMT2_OPTION.reference_name + "_", "");
			String[] list = part.split("_[0-9]_");
			if (list.length == 2)
			{
				String val1 = list[0].replaceAll("\\d*$", "");
				String val2 = list[1];
				String conNew = con.replace(val1, val2);
				ele.setTextContent(conNew);
				echoModification(change, con, conNew);
			}
		} else if (con.contains(change.getValueDefault()))
		{ // seed fault
			String val1 = change.getValueDefault();
			String val2 = change.getValueNew();
			String conNew = con.replace(val1, val2);
			ele.setTextContent(conNew);
			// System.out.println(con + " -> " + conNew);
			echoModification(change, con, conNew);
		}
	}

	@Override
	protected void triggerUpdate(Element ele)
	{
		for (Modification change : modList)
		{
			if (change.getOption() != SMT2_OPTION.RESET)
				continue;
			if (idCounter + 1 != change.getID())
				continue;

			String con = ele.getTextContent();
			String conNew = "";
			if (change.getValueDefault().compareTo("true") == 0)
				conNew = "";
			else if (change.getValueDefault().compareTo("false") == 0)
			{
				String var = getVariableName(change.getName());
				conNew = var += ":=0";
			}
			ele.setTextContent(conNew);
			echoModification(change, con, conNew);
			continue;
		}
	}

	@Override
	protected void triggerTransition(Element ele)
	{
		idCounter++;
		// if (ele.getNodeName().compareTo("transition") != 0)
		// System.out.println(idCounter + 1);
	}

	@Override
	protected void triggerUrgent(Element ele)
	{
		eleUrgent = ele;
	}

	@Override
	protected void triggerState(Element ele)
	{
		// if (ele.getNodeName().compareTo("location") != 0)
		// System.out.println(idCounter + 1);
		idCounter++;

		// todo: test
		// todo: get correct id for state
		for (Modification changeConstraint : modList)
		{
			if (changeConstraint.getOption() != SMT2_OPTION.URGENT)
				continue;
			if (idCounter != changeConstraint.getID())
				return;
			modifyUrgent(ele, changeConstraint);
		}
	}

	protected void modifyUrgent(Element ele, Modification change)
	{
		Element eu = eleUrgent;
		eleUrgent = null;
		if (eu != null)
			ele.removeChild(eu);
		else
			ele.appendChild(doc.createElement("urgent"));
	}

	@Override
	protected void triggerStateName(Element eleCur)
	{
		// System.out.println(eleCur.getTextContent());
		if (delErrorState && eleCur.getTextContent().contains("error"))
		{
			stateIgnore = true;
			errorStateList.add(textlocation);
		}
	}

	private void echoModification(Modification cC, String text, String conNew)
	{
		bMod = true;
		if (repair == null)
			repair = new Repair();
		ModifiedConstraint modCon = new ModifiedConstraint(cC.getOption(), cC.getName(), text, conNew);
		repair.addModification(modCon);
	}

	public Repair getRepair()
	{
		return repair;
	}
}
