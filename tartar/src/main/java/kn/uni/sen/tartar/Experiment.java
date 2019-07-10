package kn.uni.sen.tartar;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

import kn.uni.sen.tartar.admissible.CorruptModel;
import kn.uni.sen.tartar.admissible.FileChange;
import kn.uni.sen.tartar.admissible.Repair;
import kn.uni.sen.tartar.uppaal2smt2.ParseUPPAAL;
import kn.uni.sen.tartar.uppaal2smt2.SMT2_OPTION;
import kn.uni.sen.tartar.util.ResourceFile;
import kn.uni.sen.tartar.util.ResourceFolder;

/**
 * Add different bugs to a model and try to find all of them.
 * 
 * @author Martin Koelbl
 */
public class Experiment implements Job2
{
	String folder = "result";

	public void setFolder(String folder)
	{
		this.folder = folder;
	}

	private List<String> getInputParameter(SMT2_OPTION option, String fileTA, String fileTrace)
	{
		List<String> list = new LinkedList<>();
		list.add("-c2");
		list.add(fileTA);
		if ((fileTrace != null) && !!!fileTrace.isEmpty())
		{
			list.add("-t");
			list.add(fileTrace);
		}
		list.add(0, "-" + SMT2_OPTION.getName(option));
		// if (z3Check)
		// list.add(0, "-z3");
		return list;
	}

	String fileTA = null;
	ProgramEvent ProgramEvent = null;
	ExperimentData expData;
	UppaalApi api = new UppaalApi(false);
	SMT2_OPTION option;

	static String multiFile = null;

	public void expOption(String fileTA, String fileData, SMT2_OPTION option)
	{
		this.option = option;
		expData = new ExperimentData(option);

		// List<FileChange> files =
		corruptFile(fileTA, option);
		/*
		 * for (FileChange changes : files) { checkCorruptFile(changes); //
		 * break; }
		 */
		expData.writeAnalyse(multiFile);
		expData.writeData(fileData);
	}

	public List<FileChange> corruptFile(String fileTA, SMT2_OPTION option)
	{
		List<FileChange> list = new ArrayList<>();

		String fileName = ResourceFile.getFilenameOnly(fileTA);
		folder = "result/" + fileName;
		api.setFolder(folder);
		fileName = ResourceFile.getFilename(fileTA);
		ResourceFolder.createFolder(folder);

		String fileCopy = "";
		int constraint_max = 1;
		for (int j = 1; j <= constraint_max; j++)
		{
			// create new file
			String opt = SMT2_OPTION.getName(option);
			int max = 1;
			CorruptModel corrupt = null;
			for (int i = 1; i <= max; i++)
			{
				fileCopy = folder + "/" + fileName.replace(".xml", "_break_" + opt + "_" + j + "_" + i + ".xml");
				corrupt = new CorruptModel(fileTA, fileCopy, false);
				corrupt.corruption(option, j, i);
				ParseUPPAAL.parseFile(fileTA, corrupt);
				// System.out.println(fileCopy);

				if (max == 1)
					max = corrupt.getCorruptionCount();

				// no constraints was changed
				if (!!!corrupt.isModified())
					ResourceFile.deleteFile(fileCopy);
				else
				{
					FileChange dif = new FileChange(fileCopy, corrupt.getRepair());
					if (!!!checkCorruptFile(dif))
						continue;
					list.add(dif);
				}
			}
			if (corrupt == null)
				continue;
			if ((option == SMT2_OPTION.BOUNDARY) || (option == SMT2_OPTION.COMPARISON)
					|| (option == SMT2_OPTION.REFERENCE))
				constraint_max = corrupt.getConstraintCount();
			else if (option == SMT2_OPTION.RESET)
				constraint_max = corrupt.getTransitionCount();
			else if (option == SMT2_OPTION.URGENT)
				constraint_max = corrupt.getStateCount();
			// break;
		}
		return list;
	}

	public boolean checkCorruptFile(FileChange changes)
	{
		expData.addSeedFault(changes.getText());
		// create counterexample by uppaal
		String file = changes.getFile();
		String fileTrace = api.createCounterexample(file);
		long time = api.getUppaalTime();
		if ((fileTrace == null) || fileTrace.isEmpty())
		{
			// System.out.println(changes.getText());
			ResourceFile.deleteFile(file);
			return false;
		}

		System.out.println("----------------------");
		System.out.println("Mutated-Model-File: " + changes.getFile());
		System.out.println("Modification: " + changes.getText());
		Fault fault = expData.addFault(changes.getText(), time);

		// call diagnosis
		List<String> list = getInputParameter(option, file, fileTrace);
		MainDiagnostic md = new MainDiagnostic(expData);
		md.setFault(fault);
		md.setFolder(folder);
		md.runDiagnostic((String[]) list.toArray(new String[list.size()]));
		List<Repair> listMod = md.getRepairList();
		if (listMod != null)
			for (Repair r : listMod)
			{
				System.out.println("Repair/ " + r.getModificationText());
				// fault.addRepair(r);
			}
		System.out.println("");
		return true;
	}

	public void runExp(String fileTA)
	{
		System.gc();
		System.runFinalization();
		String name = ResourceFile.getFilenameOnly(fileTA);
		String fileData = folder + "/0exp_" + name + ".txt";
		ExperimentData.writeHead(fileData);
		if (multiFile == null)
			multiFile = ResourceFile.getUniqueFile(folder, "MultiTrace.txt");
		// run an experiment with each modification option
		// todo: include all SMT2_OPTION.ListModifier;
		SMT2_OPTION[] list = new SMT2_OPTION[] { SMT2_OPTION.BOUNDARY,
				/* SMT2_OPTION.COMPARISON , SMT2_OPTION.REFERENCE */ };
		for (SMT2_OPTION option : list)
		{
			expOption(fileTA, fileData, option);
		}
	}

	@Override
	public void start()
	{
		if (fileTA != null)
			runExp(fileTA);
		else
			System.out.println("Missing model file");
	}

	@Override
	public void setModelFile(String modelFile)
	{
		fileTA = modelFile;
	}

	@Override
	public void setTraceFile(String traceFile)
	{
	}

	@Override
	public void setOption(SMT2_OPTION opt)
	{
		if ((opt == SMT2_OPTION.BOUNDARY) || (opt == SMT2_OPTION.COMPARISON) || (opt == SMT2_OPTION.REFERENCE)
				|| (opt == SMT2_OPTION.RESET) || (opt == SMT2_OPTION.URGENT))
			option = opt;
	}

	@Override
	public void setProgramEvent(ProgramEvent programEvent)
	{
		this.ProgramEvent = programEvent;
	}
}
