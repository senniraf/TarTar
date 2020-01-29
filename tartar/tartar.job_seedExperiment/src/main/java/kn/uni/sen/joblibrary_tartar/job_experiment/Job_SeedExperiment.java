package kn.uni.sen.joblibrary_tartar.job_experiment;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import kn.uni.sen.joblibrary.tartar.admissibility.AdmissibilityCheck;
//import kn.uni.sen.joblibrary.tartar.common.ResultAdm;
import kn.uni.sen.joblibrary.tartar.common.SMT2_OPTION;
import kn.uni.sen.joblibrary.tartar.common.uppaal.UppaalApi;
import kn.uni.sen.joblibrary.tartar.convert.ParseUPPAAL;
import kn.uni.sen.joblibrary.tartar.job_repaircomputation.Repair;
import kn.uni.sen.joblibrary.tartar.modifymodel.ExperimentData;
import kn.uni.sen.joblibrary.tartar.modifymodel.Fault;
import kn.uni.sen.joblibrary.tartar.modifymodel.FileChange;
import kn.uni.sen.jobscheduler.common.impl.JobAbstract;
import kn.uni.sen.jobscheduler.common.model.JobResult;
import kn.uni.sen.jobscheduler.common.model.JobState;
import kn.uni.sen.jobscheduler.common.model.ResourceInterface;
import kn.uni.sen.jobscheduler.common.model.RunContext;
import kn.uni.sen.jobscheduler.common.resource.ResourceEnum;
import kn.uni.sen.jobscheduler.common.resource.ResourceFile;
import kn.uni.sen.jobscheduler.common.resource.ResourceFolder;
import kn.uni.sen.jobscheduler.common.resource.ResourceInteger;
import kn.uni.sen.jobscheduler.common.resource.ResourceTag;
import kn.uni.sen.jobscheduler.common.resource.ResourceType;
import kn.uni.sen.tartar.smtcall.Z3Call;
import kn.uni.sen.joblibrary.tartar.job_repaircomputation.Diagnostic;
import kn.uni.sen.joblibrary.tartar.job_repaircomputation.Job_RepairComputation;
import kn.uni.sen.joblibrary.tartar.job_repaircomputation.ProgramEvent;

/**
 * Add different bugs to a model and try to find all of them.
 * 
 * @author Martin Koelbl
 */
public class Job_SeedExperiment extends JobAbstract
{
	public static final String SEED_KIND = "SeedKind";
	public static final String FAULT = "FAULT";

	{
		createInputDescr(Job_RepairComputation.MODEL, ResourceType.FILE).addTag(ResourceTag.NECESSARY);
		createInputDescr(SEED_KIND, ResourceType.ENUM);
		createInputDescr(Job_RepairComputation.TIMEOUT_Z3, ResourceType.INTEGER);
		createInputDescr(Job_RepairComputation.REPAIR_KIND, ResourceType.ENUM);

		createResultDescr(FAULT, ResourceType.STRING);
	}

	public Job_SeedExperiment(RunContext father)
	{
		super(father);
		// setEventHandler(father);
	}

	private Diagnostic createDiagnostic()
	{
		Diagnostic diagnostic = new Diagnostic(this);
		diagnostic.setFolder(getFolderText());
		diagnostic.setLogger(2);
		diagnostic.setAdmChecker(new AdmissibilityCheck(this));
		return diagnostic;
	}

	// String fileTA = null;
	ProgramEvent ProgramEvent = null;
	Map<SMT2_OPTION, ExperimentData> expDataMap = new HashMap<>();

	UppaalApi api = null;

	SMT2_OPTION corOpt = SMT2_OPTION.UNKOWN;
	ResourceEnum repRes = null;

	String multiFile = null;
	private String fileExpData;

	int TDTsolveCount = 0; // number of repaired TDTs
	int TDTmaxRepairSum = 0; // maximal number of repairs for a TDT

	public List<FileChange> corruptFile(String fileTA, SMT2_OPTION option)
	{
		List<FileChange> list = new ArrayList<>();

		String fileName = ResourceFile.getFilenameOnly(fileTA);
		String folder = ResourceFolder.appendFolder(getFolderText(), fileName);
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
				// System.out.println(fileCopy);
				corrupt = new CorruptModel(fileTA, fileCopy, false);
				corrupt.corruption(option, j, i);
				ParseUPPAAL.parseFile(fileTA, corrupt);
				// System.out.println(fileCopy);

				if (max == 1)
					max = corrupt.getCorruptionCount();

				// no constraints was changed
				if (!!!corrupt.isModified())
					ResourceFile.removeFile(fileCopy);
				else
				{
					FileChange dif = new FileChange(fileCopy, corrupt.getRepair());
					if (!!!checkCorruptFile(dif, fileTA))
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

	ExperimentData getDataExp(SMT2_OPTION optRep)
	{
		ExperimentData exp = expDataMap.get(optRep);
		if (exp != null)
			return exp;
		exp = new ExperimentData(corOpt, optRep);
		expDataMap.put(optRep, exp);
		return exp;
	}

	private void addSeedFault(FileChange changes)
	{
		ResourceEnum res = this.repRes;
		while (res != null)
		{
			SMT2_OPTION optRep = getRepairTypeOpt(res.getData());
			res = (ResourceEnum) res.getNext();
			if (optRep == SMT2_OPTION.UNKOWN)
				continue;
			ExperimentData expData = getDataExp(optRep);
			expData.addSeedFault(changes.getText());
		}
	}

	public boolean checkCorruptFile(FileChange changes, String fileOrg)
	{
		// create counterexample by uppaal
		String file = changes.getFile();
		String fileTrace = api.createCounterexample(file);
		long time = api.getUppaalTime();
		if ((fileTrace == null) || fileTrace.isEmpty())
		{
			// System.out.println(changes.getText());
			addSeedFault(changes);
			ResourceFile.removeFile(file);
			return false;
		}
		boolean TDTsolved = false; // current TDT repaired?
		int repairAdmSum = 0;

		logInfo("----------------------");
		logInfo("Mutated-Model-File: " + changes.getFile());
		logInfo("Modification: " + changes.getText());

		//AdmissibilityCheck check = new AdmissibilityCheck(this);
		//String val = "in";
		//ResultAdm adm = check.checkEquivalence(fileOrg, changes.getFile());
		//if (adm == null)
		//	val = "unkown ";
		//if ((adm != null) && adm.isAdmisible())
		//	val = "";

		// call diagnosis
		ResourceEnum res = this.repRes;
		while (res != null)
		{
			SMT2_OPTION optRep = getRepairTypeOpt(res.getData());
			res = (ResourceEnum) res.getNext();
			if (optRep == SMT2_OPTION.UNKOWN)
				continue;

			ExperimentData expData = getDataExp(optRep);
			expData.addSeedFault(changes.getText());
			Fault fault = expData.addFault(changes.getText(), time);
			Diagnostic md = createDiagnostic();
			//md.getLogger().logEvent("Corruption is " + val + "admissibile");
			md.setFault(fault);
			md.setFolder(getFolderText());

			md.diagnostic(file, fileTrace, optRep);
			int sc = md.getSolvedCount();
			repairAdmSum += sc;
			if ((sc != 0) && !!!TDTsolved)
			{
				TDTsolved = true;
				TDTsolveCount++;
			}
			List<Repair> listMod = md.getRepairList();
			if (listMod != null)
				for (Repair r : listMod)
				{
					logInfo("Repair/ " + r.getModificationText());
					// fault.addRepair(r);
				}
			logInfo("");
		}
		if (TDTmaxRepairSum < repairAdmSum)
			TDTmaxRepairSum = repairAdmSum;
		return true;
	}

	public void runExp(String fileTA)
	{
		System.gc();
		System.runFinalization();
		String name = ResourceFile.getFilenameOnly(fileTA);
		String folder = getFolderText();
		String path = "";
		if ("result".equals(folder))
			path = folder + "/";

		fileExpData = path + "experiment_analysis.txt";
		System.out.println("Start experiment " + name);
		if (!!!ResourceFile.exists(fileExpData))
		{
			ResourceFile.writeText2File(fileExpData, "");
			ExperimentData.writeHead(fileExpData);
		}
		if (multiFile == null)
			multiFile = ResourceFile.getUniqueFile(folder, "MultiTrace.txt");
		// run an experiment with each modification option
		TDTsolveCount = 0; // number of TDTs with admissible repairs
		corruptFile(fileTA, corOpt);
		
		for (Entry<SMT2_OPTION, ExperimentData> entry : expDataMap.entrySet())
		{
			ExperimentData expData = entry.getValue();
			expData.writeAnalyse(multiFile);
			expData.writeData(fileExpData, name, TDTsolveCount, TDTmaxRepairSum);
		}
	}

	@Override
	public JobState task()
	{
		ResourceFile modelFile = getResourceWithType(Job_RepairComputation.MODEL, false);
		if (modelFile == null)
			return endError("Missing model file!");

		ResourceEnum corEnum = getResourceWithType(SEED_KIND, false);
		if (corEnum != null)
			corOpt = getRepairTypeOpt(corEnum.getData());
		// logger.log(DEBUG, corEnum.getData()+" "+corOpt);

		ResourceInteger time = getResourceWithType(Job_RepairComputation.TIMEOUT_Z3, false);
		if (time != null)
		{
			int timeVal = time.getDataValue();
			if (timeVal > 0)
				Z3Call.timeout = timeVal * 1000;
		}

		//todo: repRes = getResourceWithType(Job_RepairComputation.REPAIR_KIND, false);
		repRes = new ResourceEnum(SMT2_OPTION.BOUNDARY);
		repRes.addNext(new ResourceEnum(SMT2_OPTION.RESET)); 
		repRes.addNext(new ResourceEnum(SMT2_OPTION.URGENT)); 
		repRes.addNext(new ResourceEnum(SMT2_OPTION.COMPARISON)); 
		repRes.addNext(new ResourceEnum(SMT2_OPTION.REFERENCE)); 
		

		if (api == null)
			api = new UppaalApi(this, false);

		Z3Call.timeout = 120000; // 600 = 10 min /org: 120 sec
		runExp(modelFile.getData());
		return end(JobResult.OK);
	}

	private SMT2_OPTION getRepairTypeOpt(String data)
	{
		if (data == null)
			return SMT2_OPTION.UNKOWN;
		SMT2_OPTION opt = SMT2_OPTION.valueOf(data);
		return isRepairTypeOption(opt);
	}

	public SMT2_OPTION isRepairTypeOption(SMT2_OPTION opt)
	{
		if (opt == null)
			return SMT2_OPTION.UNKOWN;
		if ((opt == SMT2_OPTION.BOUNDARY) || (opt == SMT2_OPTION.COMPARISON) || (opt == SMT2_OPTION.REFERENCE)
				|| (opt == SMT2_OPTION.RESET) || (opt == SMT2_OPTION.URGENT))
			return opt;
		return SMT2_OPTION.UNKOWN;
	}

	@Override
	public ResourceInterface getResultResource(String name)
	{
		if (FAULT.equals(name))
		{
			// todo: implement
			return null;
		}
		return super.getResultResource(name);
	}
}
