package kn.uni.sen.tartar.admissible;

import kn.uni.sen.tartar.smtcall.ModelSolution;
import kn.uni.sen.tartar.uppaal2smt2.ParseUPPAAL;
import kn.uni.sen.tartar.util.ResourceFile;

/**
 * Checks if a solution is admissible to an NTA Admit repair on NTA and deletes
 * all error transitions
 * 
 * @author Martin Koelbl
 */
public class CheckAdmissibility
{
	public static Repair checkAdmissibility(String fileTA, ModelSolution sol, String folder)
	{
		if (!!!folder.isEmpty())
			folder = folder + "/";

		String fileName = ResourceFile.getFilename(fileTA);
		String fileTA_comp = folder + fileName.replace(".xml", "_comp.xml");
		String fileTA_repair = folder + fileName.replace(".xml", "_rep.xml");
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

		// System.out.println(sol.toText());
		// parse file and write it back to a tmp file

		// delete error transition towards state "error"

		// check admissibility
		EquivalenceCheck check = new EquivalenceCheck();
		ResultAdm ret = check.checkEquivalence(fileTA_comp, fileTA_repair, folder);

		// ArrayList<Integer> list = new ArrayList<>();
		// for (int i = 0; i < 5000; i++)
		// list.add(i);
		repair.setAdmissible(ret);
		return repair;
	}
}
