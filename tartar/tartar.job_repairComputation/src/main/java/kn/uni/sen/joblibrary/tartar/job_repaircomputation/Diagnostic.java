package kn.uni.sen.joblibrary.tartar.job_repaircomputation;

import java.util.ArrayList;
import java.util.List;

import kn.uni.sen.tartar.smtcall.JavaSmtCall;
import kn.uni.sen.tartar.smtcall.ModelSolution;
import kn.uni.sen.tartar.smtcall.SMTCall;
import kn.uni.sen.tartar.smtcall.Z3Call;
import kn.uni.sen.joblibrary.tartar.common.CheckAdmissibility;
import kn.uni.sen.joblibrary.tartar.common.ResultAdm;
import kn.uni.sen.joblibrary.tartar.common.SMT2_OPTION;
import kn.uni.sen.joblibrary.tartar.common.uppaal.UppaalApi;
import kn.uni.sen.joblibrary.tartar.common.util.CheckJavaMemory;
import kn.uni.sen.joblibrary.tartar.convert.Ut2Smt2;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.ConstraintSmt2;
import kn.uni.sen.joblibrary.tartar.modifymodel.Fault;
import kn.uni.sen.joblibrary.tartar.modifymodel.ModifyModel;
import kn.uni.sen.jobscheduler.common.model.RunContext;
import kn.uni.sen.jobscheduler.common.model.JobEvent;
import kn.uni.sen.jobscheduler.common.resource.ResourceFile;
import kn.uni.sen.jobscheduler.common.resource.ResourceFolder;

/**
 * This file does real diagnosis
 * 
 * @author Martin Koelbl
 */
public class Diagnostic
{
	boolean use_uppaal = false;

	// diagnostic is done with quantifier elimination or directly by creating
	// the model as a function
	protected boolean use_qe = true;
	boolean shorter = true; // decrement length of trace

	// all options are set in MainDiagnostic
	boolean optionZ3 = false;
	String optionName;
	SMT2_OPTION option; // = new HashSet<>();
	SMT2_SOLVER solver = SMT2_SOLVER.Z3;
	String modelName = "";
	String fileTrace = "";
	String fileModel = "";
	ConstraintSmt2 property;
	int commentDepth = 1;

	List<Repair> repairList = null; // todo: only delete this list

	// template of destinyFile
	String destinyFile;
	String modTraceFile;

	EventLogger eventLogger = null;
	Fault fault = null;

	double maxZ3 = 0.0;
	int lengthTrace = 0;
	int varCount = 0;
	int assertCount = 0;
	String folder = "";

	CheckAdmissibility admChecker = null;

	CheckJavaMemory memCheck = new CheckJavaMemory();

	RunContext context;

	int solveCount = 0;

	public Diagnostic(RunContext context)
	{
		this.context = context;
		folder = context.getFolderText();
		eventLogger = new EventLogger(true, context);
	}

	public void setFault(Fault fault)
	{
		this.fault = fault;
	}

	public Ut2Smt2 createConverter()
	{
		modelName = ResourceFile.getFilenameOnly(fileModel);
		modelName += ".smt2";
		String destFile = ResourceFolder.appendFolder(folder, modelName);
		return new Ut2Smt2(fileTrace, fileModel, destFile, context);
	}

	/*
	 * private String getFilenameModel(String modelFile) { String file =
	 * modelFile.replace(".xml", ".smt2"); int index = file.lastIndexOf("/"); if
	 * (index != -1) file = file.substring(index + 1); return file; }
	 */

	public List<Repair> getRepairList()
	{
		return repairList;
	}

	protected Repair modifyFile(String fileOrg, ModelSolution sol)
	{
		int index = repairList.size() + 1;
		Repair repair = ModifyModel.modifyModel(fileOrg, sol, folder, index);

		if (admChecker == null)
			return repair;
		// System.out.print("Solution: " + sol.toText());

		memCheck.checkJavaMemory();
		if (repair == null)
			return null;
		String fileMod = repair.getRepairedFile();
		ResultAdm admRes = admChecker.checkEquivalence(fileOrg, fileMod);
		repair.setAdmissible(admRes);
		memCheck.check(admChecker.getMemory());
		String text = "";
		if (repair.isAdmissible())
			text = "Admissible: ";
		else
			text = "Inadmissible: ";

		EventLog ev = new EventLog(text);
		ev.addEventValue("Max", memCheck.getMem(), "MB");
		if (!!!repair.isAdmissible())
			ev.addEventValue("" + repair.getCounterTrace());
		System.gc();
		System.runFinalization();
		memCheck.reset();
		eventLogger.logEvent(ev);

		eventLogger.logEvent("TTS " + admChecker.getTimeSpace1() + "ms");
		eventLogger.logEvent("TTS " + admChecker.getTimeSpace2() + "ms");

		// System.out.println(text + sol.toText());
		return repair;
	}

	long start = 0;
	long timeRepairLast = System.currentTimeMillis();

	public boolean diagnostic(String fileModel, String fileTrace, SMT2_OPTION option)
	{
		this.fileModel = fileModel;
		this.option = option;
		solveCount = 0;

		repairList = new ArrayList<>();
		// 1. run uppaal if necessary
		if ((fileTrace == null) || fileTrace.isEmpty())
		{
			fileTrace = (new UppaalApi(context)).createCounterexample(fileModel);
			if ((fileTrace == null) || fileTrace.isEmpty() || !!!ResourceFile.exists(fileTrace))
			{
				context.logEventStatus(JobEvent.ERROR, "Missing counterexample trace file.");
				return end(false);
			}
		}
		this.fileTrace = fileTrace;

		EventLog evS = eventLogger.logEvent("startRepairDiagnosis");
		if (fault != null)
			evS.addEventValue(" " + fault.getFault());
		start = evS.getTime();
		if (option == null)
		{
			return transform2Trace();
		}

		String z3RepairFile = "";
		if (use_qe)
		{
			// 2. parse counterexample trace and model and add modification of
			// trace
			if (!!!createFilesModifiedTracesByQE())
				return end(false);
			eventLogger.logEvent("create QE file");

			// 3. run z3 for quantifier elimination
			SMTCall z3 = createSMTSolver();
			if (!!!z3.runEliminationFile(destinyFile))
			{
				context.logEventStatus(JobEvent.ERROR, "Run QE failed");
				if (fault != null)
					fault.setTimeQE(z3.getTime());
				return end(false);
			}
			timeRepairLast = System.currentTimeMillis();
			if (fault != null)
				fault.setTimeQE(z3.getTime());
			double mem = z3.getMemory();
			if (mem > maxZ3)
				maxZ3 = mem;
			eventLogger.logValue("QE endend: ", "", mem, "MB");

			// 4. combine quantifier eliminated trace and modified trace
			z3RepairFile = combineTraceFilesQE(z3.getEliminatedModel(), modTraceFile, destinyFile);
			eventLogger.logEvent("create diagnosis file");
		} else if (!!!use_qe)
		{
			z3RepairFile = createReplaceAll();
		} else
		{
			context.logEventStatus(JobEvent.ERROR, "Error: Imply is depricated and was removed");
			return end(true);
		}

		// 5. loop for finding solution
		// 5.1 find solution
		eventLogger.logEvent("Search solutions");
		List<ModelSolution> solList = new ArrayList<>();
		ModelSolution sol = searchSolution(z3RepairFile, solList, "Search repair 1: ");
		ModelSolution solLast = null;
		while ((sol != null) && (!!!sol.getChangeList().isEmpty()) && (!!!ModelSolution.contained(solList, sol)))
		{
			// 5.2 assert solution
			solList.add(sol);

			// 5.3 interpret and depict solution
			long timeAdmStart = System.currentTimeMillis();
			eventLogger.logEvent("Modify file");
			Repair repair = modifyFile(fileModel, sol);

			if (repair != null)
			{
				long time = System.currentTimeMillis();
				long timeAdmTmp = time - timeAdmStart;
				repair.setTimeRepair(time - timeRepairLast - timeAdmTmp);
				repair.setTimeAdm(timeAdmTmp);
				timeRepairLast = time;
				if (fault != null)
					fault.addRepair(repair);
			}
			repairList.add(repair);
			if (repair.isAdmissible())
				solveCount++;

			if (fault != null)
				fault.addRepair(repair);

			// eventLogger.logEvent("Checked admissibility");

			// same solution found again
			if ((solLast != null) && solLast.contains(sol))
				// error: should not happen
				break;

			// 5.1 find solution
			sol = searchSolution(z3RepairFile, solList, "Search repair " + (solList.size() + 1) + ": ");
		}

		if (sol == null)
			return end(false);
		return end(true);
	}

	boolean end(boolean ret)
	{
		EventLog evE = new EventLog("endRepairDiagnosis");
		evE.addEventValue("", memCheck.getMaxMem(), "MB");
		eventLogger.logEvent(evE);
		eventLogger.end();
		if (fault != null)
		{
			fault.setMemory(memCheck.getMaxMem());
			fault.setMemoryZ3(maxZ3);
			fault.setVarZ3(varCount);
			fault.setAssertZ3(assertCount);
			fault.setMaxTraceLength(lengthTrace);
		}
		String opt = SMT2_OPTION.getName(option);
		eventLogger.save2File(folder + "/" + modelName + "_diagnostic_" + opt + ".txt");
		return ret;
	}

	public EventLogger getLogger()
	{
		return eventLogger;
	}

	private boolean transform2Trace()
	{
		Ut2Smt2 converter = createConverter();
		if (converter.convert())
		{
			System.out.println("Conversion with modification failed.");
			return false;
		}
		property = converter.getProperty();
		modTraceFile = converter.getDestinyFile();
		return true;
	}

	private String createReplaceAll()
	{
		Ut2Smt2 converter = createConverter();
		converter.setOption(SMT2_OPTION.APPEND);
		// converter.setOption(SMT2_OPTION.DEL_PROP);
		converter.setOutput(SMT2_OPTION.SINGLE_ASSERT);
		if (option != null)
			converter.setOption(option);
		if (!!!converter.convert())
		{
			context.logEventStatus(JobEvent.ERROR, "Conversion with quantifier elimination failed.");
			return null;
		}
		modTraceFile = converter.getDestinyFile();
		String text = ResourceFile.parseFile(modTraceFile);

		converter = createConverter();
		converter.setOption(SMT2_OPTION.DEL_PROP);
		if (option != null)
			converter.setOption(option);
		if (!!!converter.convert())
		{
			context.logEventStatus(JobEvent.ERROR, "Conversion with quantifier elimination failed.");
			return null;
		}
		property = converter.getProperty();
		lengthTrace = converter.getTraceLength();
		destinyFile = converter.getDestinyFile();

		int index = 0;
		while (index >= 0)
		{
			index = text.indexOf("(declare-const _bv", index);
			if (index < 0)
				break;
			int end = text.indexOf("\n", index);
			String text2 = text.substring(0, index - 1);
			if (end >= 0)
				text2 += text.substring(end + 1);
			String del = text.substring(index, end);
			System.out.println(del);
			text = text2;
		}
		// String prop = property.getTextSmt2();
		// text += "\n(assert (not" + prop + "));";
		ResourceFile.appendText2File(destinyFile, text);

		return destinyFile;
	}

	private boolean createFilesModifiedTracesByQE()
	{
		Ut2Smt2 converter = createConverter();
		converter.setOutput(SMT2_OPTION.ELIMINATION);
		converter.setOption(SMT2_OPTION.DEL_PROP);
		if (option != null)
			converter.setOption(option);
		if (!!!converter.convert())
		{
			context.logEventStatus(JobEvent.ERROR, "Conversion with quantifier elimination failed.");
			return false;
		}
		lengthTrace = converter.getTraceLength();
		destinyFile = converter.getDestinyFile();

		converter = createConverter();
		converter.setOption(SMT2_OPTION.DEL_PROP);
		converter.setOption(option);
		if (!!!converter.convert())
		{
			context.logEventStatus(JobEvent.ERROR, "Conversion with modifiaction failed.");
			return false;
		}
		property = converter.getProperty();
		modTraceFile = converter.getDestinyFile();
		return true;
	}

	/**
	 * Combines the quantifier eliminated trace and the modified trace
	 * 
	 * @param qeFile
	 * 
	 * @param string
	 * @param model
	 */
	private String combineTraceFilesQE(String qe_model, String modTraceFile, String qeFile)
	{
		String diagFile = modTraceFile.replace(".smt2", "_diag.smt2");
		ResourceFile.copyFile(modTraceFile, diagFile);

		if (qe_model == null)
			return null;

		String notProp = "";
		if (property != null)
		{
			// System.out.println(property.getTextSmt2());
			// todo: not necessary for error encoding
			// ConstraintSmt2 not = new ConstraintSmt2("not", property);
			notProp = "\n\n  " + property.getTextSmt2();
			notProp = exchangeClocks(notProp);
		} else
			System.out.println("Warning: property is missing!");

		String qeTrace = "\n  " + qe_model.toString();

		String text = "(assert (and  " + qeTrace + "))";

		// System.out.println(qeTrace);
		ResourceFile.appendText2File(diagFile, text);
		return diagFile;
	}

	/**
	 * After quantifier elimination no clocks are in formula anymore so all
	 * clocks need to be expressed by delays
	 * 
	 * @param prop
	 * @return String without clock
	 */
	private String exchangeClocks(String prop)
	{
		// todo: check when was last reset of clock
		// better is a quantifier elimination on the property
		String[] list = prop.split(" ");
		String res = "";
		for (String s : list)
		{
			if (s.length() >= 2)
			{
				String last = s.substring(s.length() - 1);
				int val = 0;
				try
				{
					val = Integer.parseInt(last);
					if (val == 1)
						s = "0.0";
					else
					{
						s = "";
						if (val >= 3)
							s = "(+";
						for (int i = 1; i < val; i++)
						{
							s += " _d" + i;
						}
						if (val >= 3)
							s += ") ";
						s += " ";
					}
				} catch (Exception ex)
				{
				}
			}
			res += s;
		}
		return res;
	}

	private ModelSolution searchSolution(String diagFile, List<ModelSolution> solList, String event)
	{
		SMTCall z3 = createSMTSolver();
		ModelSolution ret = z3.runFileSoft(diagFile, solList);
		EventLog ev = new EventLog(event);
		double mem = z3.getMemory();
		if (mem > maxZ3)
			maxZ3 = mem;
		int count = z3.getVarCount();
		if (count > varCount)
			varCount = count;
		count = z3.getAssertCount();
		if (count > assertCount)
			assertCount = count;
		ev.addEventValue("", z3.getMemory(), "MB");

		if (ret == null)
		{
			eventLogger.logEvent(ev);
			return ret;
		}
		// Model m = z3.getModel();
		// System.out.println(m);
		ev.addEventValue(ret.toText());
		eventLogger.logEvent(ev);
		return ret;
	}

	public void setAdmChecker(CheckAdmissibility checker)
	{
		this.admChecker = checker;
		eventLogger.setAdm(checker);
	}

	private SMTCall createSMTSolver()
	{
		if (solver == SMT2_SOLVER.Z3)
			return new Z3Call();
		if (solver == SMT2_SOLVER.JAVA_SMT_Z3)
			return new JavaSmtCall();
		return null;
	}

	public void setFolder(String folder)
	{
		this.folder = folder;
	}

	public void setLogger(int index)
	{
		// todo: implement
	}

	public void setZ3(boolean z3)
	{
		optionZ3 = z3;
	}

	public int getSolvedCount()
	{
		return solveCount;
	}
}
