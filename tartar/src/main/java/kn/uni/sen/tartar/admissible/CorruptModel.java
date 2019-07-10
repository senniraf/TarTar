package kn.uni.sen.tartar.admissible;

import java.util.ArrayList;
import java.util.List;

import org.w3c.dom.Element;

import kn.uni.sen.tartar.smtcall.Modification;
import kn.uni.sen.tartar.uppaal2smt2.ParseUPPAAL;
import kn.uni.sen.tartar.uppaal2smt2.SMT2_OPTION;
import kn.uni.sen.tartar.uppaal2smt2.smt2modify.Smt2ModComparison;
import kn.uni.sen.tartar.uppaal2smt2.uppaalmodel.model.Model;
import kn.uni.sen.tartar.uppaal2smt2.uppaalmodel.model.Template;

/**
 * Corrupts some constraints/elements in an NTA
 * 
 * @author Martin Koelbl
 */
public class CorruptModel extends ModifyModel
{
	String fileOrg;

	int maxBound = 0;

	int countConstraint = 0;
	int countTrans = 0;
	int countState = 0;

	static String fileLast = null;
	static int maxLast = 0;

	public CorruptModel(String file, String fileCopy, boolean delErrorState)
	{
		super(fileCopy, null, delErrorState);
		fileOrg = file;
		int max = maxLast;

		if (fileLast != file)
		{
			max = getMaxBound();
			fileLast = file;
			maxLast = max;
		}
		int max2 = max / 10;
		if (max <= 10)
		{
			max = 10;
			max2 = 5;
		}

		bv_list = new Integer[] { -10, -1, 1, max2, max };
		// for (Integer val : bv_list)
		// System.out.println("" + val);
	}

	int corruptCount = 1;
	int corruptReset = 1;
	Integer[] bv_list = {};
	String[] clockList = new String[] {};

	public int getCorruptionCount()
	{
		return corruptCount;
	}

	public void setCorruptionCount(SMT2_OPTION option, Template templ)
	{
		if (option == SMT2_OPTION.BOUNDARY)
			corruptCount = bv_list.length;
		if (option == SMT2_OPTION.COMPARISON)
			corruptCount = Smt2ModComparison.opList.length;
		if (option == SMT2_OPTION.RESET)
		{
			if (clockList.length == 0)
				clockList = getClockList();
			corruptCount = clockList.length;
		}
		if (option == SMT2_OPTION.REFERENCE)
		{
			// todo: List<String> clockList = templ.getClocks();
			corruptReset = clockList.length;
			if (clockList.length == 0)
				clockList = getClockList();
			corruptCount = clockList.length * (clockList.length - 1);
		}
	}

	private String[] getClockList()
	{
		Model model = new ParseUPPAAL<Model>().parseFile(fileOrg, new Model());
		return model.getClockList().toArray(new String[] {});
	}

	private int getMaxBound()
	{
		Model model = new ParseUPPAAL<Model>().parseFile(fileOrg, new Model());
		if (model == null)
			return 0;
		return model.getMaxBound();
	}

	public List<Modification> getCorruption(SMT2_OPTION option, int id, int index)
	{
		List<Modification> list = new ArrayList<>();
		Modification mod = null;
		if (option == SMT2_OPTION.BOUNDARY)
			mod = new Modification(option, id, index, bv_list[index - 1].toString());
		if (option == SMT2_OPTION.COMPARISON)
			mod = new Modification(option, id, index, Smt2ModComparison.opList[index - 1]);
		if (option == SMT2_OPTION.REFERENCE)
		{
			if (clockList.length == 0)
				clockList = getClockList();
			if (clockList.length == 0)
				return list;

			int count = clockList.length - 1;
			if (count == 0)
				return list;
			int line = (index - 1) / count;
			int it = (index - 1) % count;
			int index2 = it + (it >= line ? 1 : 0);
			// System.out.println(clockList[line] + " " + clockList[index2]);
			mod = new Modification(option, id, index, clockList[line]);
			mod.setDefaultValue(clockList[index2]);
		}
		if (mod != null)
			list.add(mod);
		return list;
	}

	public int getConstraintCount()
	{
		return countConstraint;
	}

	public int getTransitionCount()
	{
		return countTrans;
	}

	public int getStateCount()
	{
		return countState;
	}

	@Override
	protected void triggerConstraint(Element ele)
	{
		countConstraint++;
		for (Modification changeConstraint : modList)
		{
			// counter is incremented at end of node
			if (changeConstraint.getID() != countConstraint)
				continue;
			// System.out.println(countConstraint + 1);
			if (corruptCount == 1)
				setCorruptionCount(changeConstraint.getOption(), null);

			if (changeConstraint.getOption() == SMT2_OPTION.BOUNDARY)
				modifyBound(ele, changeConstraint);
			else if (changeConstraint.getOption() == SMT2_OPTION.COMPARISON)
				modifyComparison(ele, changeConstraint);
			else if (changeConstraint.getOption() == SMT2_OPTION.REFERENCE)
				modifyReference(ele, changeConstraint);
		}
	}

	@Override
	protected void triggerTransition(Element ele)
	{
		idCounter++;
		countTrans++;
		// if (ele.getNodeName().compareTo("transition") != 0)
		// System.out.println(idCounter + 1);
	}

	@Override
	protected void triggerState(Element ele)
	{
		// if (ele.getNodeName().compareTo("location") != 0)
		// System.out.println(idCounter + 1);
		countState++;
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

	public void corruption(SMT2_OPTION option, int j, int i)
	{
		modList = getCorruption(option, j, i);
	}
}
