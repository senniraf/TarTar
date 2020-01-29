package kn.uni.sen.joblibrary.tartar.modifymodel;

import java.util.ArrayList;
import java.util.List;

import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;

import kn.uni.sen.joblibrary.tartar.common.SMT2_OPTION;
import kn.uni.sen.joblibrary.tartar.convert.ParseUPPAAL;
import kn.uni.sen.joblibrary.tartar.convert.smt2modify.Smt2ModComparison;
import kn.uni.sen.jobscheduler.common.resource.ResourceFile;
import kn.uni.sen.joblibrary.tartar.job_repaircomputation.Repair;
import kn.uni.sen.tartar.smtcall.ModelSolution;
import kn.uni.sen.tartar.smtcall.Modification;

public class ModifyModel extends CloneModel
{
	protected List<Modification> modList;

	protected int idCounter = 0; // counts states and transitions
	Repair repair = null; // shows modidies constraint
	Element eleUrgent = null;

	protected boolean bMod = false;
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
		if (op == null)
			return;
		// if ((con == null) || (op == null) || (opNew == null))
		// {
		// System.out.print("");
		// }
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

	protected void modifyReset(Element trans, Modification change)
	{
		String mod = change.getValueNew();
		if (("false".equals(mod)) || ("true".equals(mod)))
		// ensures modification is a repair
		{
			String var = getVariableName(change.getName());
			String con = "";
			String conNew = "";
			if (change.getValueDefault().compareTo("true") == 0)
			{
				for (Node node : getChildAttr(trans, "label", "kind", "assignment"))
				{
					con = node.getTextContent();
					conNew = var;
					if (con.contains(var))
					{
						trans.removeChild(node);
						echoModification(change, con, conNew);
					}
				}
			} else if (change.getValueDefault().compareTo("false") == 0)
			{
				Element ele2 = doc.createElement("label");
				ele2.setAttribute("kind", "assignment");
				trans.appendChild(ele2);
				conNew = var + ":=0";
				ele2.setTextContent(conNew);
				echoModification(change, var, conNew);
			}
			return;
		}
		// corruptions is derivated in Class CorruptModel
	}

	protected List<Node> getChildAttr(Element node, String name, String attr, String attrVal)
	{
		List<Node> list = new ArrayList<>();
		NodeList l = node.getElementsByTagName(name);
		Node ele = null;
		for (int i = 0; i < l.getLength(); i++)
		{
			ele = l.item(i);
			Node me = ele.getAttributes().getNamedItem(attr);
			if (me == null)
				continue;
			if (!!!attrVal.equals(me.getTextContent()))
				continue;
			list.add(ele);
		}
		return list;
	}

	@Override
	protected void triggerUpdate(Element ele)
	{
	}

	@Override
	protected void triggerTransition(Element ele)
	{
		idCounter++;
		for (Modification change : modList)
		{
			if (change.getOption() != SMT2_OPTION.RESET)
				continue;
			if (idCounter != change.getID())
				continue;
			modifyReset(ele, change);
			continue;
		}
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
		String conNew = "";
		if (eu != null)
		{
			conNew = "not urgent";
			ele.removeChild(eu);
		} else
		{
			conNew = "urgent";
			ele.appendChild(doc.createElement("urgent"));
		}
		// System.out.print(this.textlocation);
		if (textlocation == null)
			textlocation = "";
		echoModification(change, textlocation, conNew);
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

	protected void echoModification(Modification cC, String text, String conNew)
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

	public static Repair modifyModel(String fileTA, ModelSolution sol, String folder, int index)
	{
		if (!!!folder.isEmpty())
			folder = folder + "/";

		String fileName = ResourceFile.getFilename(fileTA);
		String fileTA_comp = folder + fileName.replace(".xml", "_comp.xml");
		String fileTA_repair = folder + fileName.replace(".xml", "_rep" + index + ".xml");
		// System.out.println(sol.toText());

		ModifyModel parser1 = new ModifyModel(fileTA_comp, (new ModelSolution()).getChangeList(), true);
		ModifyModel parser2 = new ModifyModel(fileTA_repair, sol.getChangeList(), true);
		ParseUPPAAL.parseFile(fileTA, parser1);
		ParseUPPAAL.parseFile(fileTA, parser2);

		Repair repair = parser2.getRepair();
		if (!!!parser2.isModified() || (repair == null))
		// repair = new Repair();
		{
			System.out.println("Error: " + sol.toText() + " is not applied!");
			return null;
		}

		repair.setRepairedFile(fileTA_repair);
		// repair.setAdmissible(ret);
		return repair;
	}
}
