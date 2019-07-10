package kn.uni.sen.tartar;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

import kn.uni.sen.tartar.admissible.CheckAdmissibility;
import kn.uni.sen.tartar.admissible.EquivalenceCheck;
import kn.uni.sen.tartar.admissible.Repair;
import kn.uni.sen.tartar.smtcall.JavaSmtCall;
import kn.uni.sen.tartar.smtcall.ModelSolution;
import kn.uni.sen.tartar.smtcall.SMTCall;
import kn.uni.sen.tartar.smtcall.Z3Call;
import kn.uni.sen.tartar.uppaal2smt2.SMT2_OPTION;
import kn.uni.sen.tartar.uppaal2smt2.Ut2Smt2;
import kn.uni.sen.tartar.uppaal2smt2.smt2.model.ConstraintSmt2;
import kn.uni.sen.tartar.util.Helper;
import kn.uni.sen.tartar.util.ResourceFile;

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
	boolean use_qe = true;
	boolean use_func = false;
	boolean use_state_qe = false; // test version: each state is qe
	boolean use_interpol = false; // test version with interpolation

	boolean shorter = true; // decrement length of trace

	ProgramStatus status = ProgramStatus.WAIT;

	// all options are set in MainDiagnostic
	boolean optionZ3 = false;
	String optionName;
	SMT2_OPTION option; // = new HashSet<>();
	SMT2_SOLVER solver = SMT2_SOLVER.Z3;
	String modelName = "";
	String fileTrace = "";
	String fileModel = "";
	String folderDestiny = "result";
	ConstraintSmt2 property;
	int commentDepth = 1;

	List<Repair> repairList = null; // todo: only delete this list

	// template of destinyFile
	String destinyFile;
	String modTraceFile;

	EventLogger eventLogger = new EventLogger(true);
	Fault fault = null;

	double maxZ3 = 0.0;
	int lengthTrace = 0;
	int varCount = 0;
	int assertCount = 0;

	public Diagnostic()
	{
	}

	public void setFault(Fault fault)
	{
		this.fault = fault;
	}

	public List<String> getTestInputParameters()
	{
		List<String> list = new LinkedList<>();
		list.add("-c2");

		list.add(fileTrace);
		list.add(fileModel);

		String folder = "";
		if ((folderDestiny != null) || !!!folderDestiny.isEmpty())
		{
			Helper.createFolder(folderDestiny);
			folder = folderDestiny + "/";
		}
		modelName = getFilenameModel(fileModel);
		list.add(folder + modelName);
		modelName = modelName.replace(".smt2", "");
		return list;
	}

	private String getFilenameModel(String modelFile)
	{
		String file = modelFile.replace(".xml", ".smt2");
		int index = file.lastIndexOf("/");
		if (index != -1)
			file = file.substring(index + 1);
		return file;
	}

	boolean diagnostic()
	{
		setProgramStatus(ProgramStatus.RUN);
		boolean ret = diagnosticReal();
		setProgramStatus(ProgramStatus.STOP);
		return ret;
	}

	public List<Repair> getRepairList()
	{
		return repairList;
	}

	protected void setProgramStatus(ProgramStatus status)
	{
		this.status = status;
	}

	protected Repair checkAdmissible(String file, ModelSolution sol)
	{
		// System.out.print("Solution: " + sol.toText());
		EquivalenceCheck.diagnostic = this;
		Repair repair = CheckAdmissibility.checkAdmissibility(file, sol, folderDestiny);
		checkJavaMemory();
		if (repair == null)
			return null;
		String text = "";
		if (repair.isAdmissible())
			text = "Admissible: ";
		else
			text = "Inadmissible: ";

		EventLog ev = new EventLog(text);
		ev.addEventValue("Max", mem, "MB");
		if (!!!repair.isAdmissible())
			ev.addEventValue("" + repair.getCounterTrace());
		System.gc();
		System.runFinalization();
		mem = 0;
		eventLogger.logEvent(ev);

		// System.out.println(text + sol.toText());
		return repair;
	}

	Runtime instance = Runtime.getRuntime();
	double maxMem = 0.0;
	double mem = 0.0;

	public void checkJavaMemory()
	{
		double mem2 = instance.totalMemory() - instance.freeMemory();
		mem2 /= (1024 * 1024);
		if (mem2 > mem)
		{
			mem = mem2;
			if (mem2 > maxMem)
				maxMem = mem2;
		}
	}

	private void addExists_Func(String modTraceFile2, String diagFile)
	{
		// the TTS version using a function "Pi" is missing the exists statement
		String data = Helper.parseFile(modTraceFile2);
		int index = data.lastIndexOf("(Pi");
		int index2 = data.indexOf(")", index);
		if ((index > 0) && (index2 > 0))
		{
			String s = data.substring(index, index2 + 1);
			index = data.indexOf("(assert-soft");
			if (index > 0)
			{
				String start = data.substring(0, index - 1);
				String end = data.substring(index);
				data = start + "\n(assert " + s + ")\n\n" + end;
			}
		} else
			System.out.println("Waning: Missing function Pi in diagnose file.");
		Helper.writeText2File(diagFile, data);
	}

	long start = 0;
	long timeRepairLast = System.currentTimeMillis();

	private boolean diagnosticReal()
	{
		repairList = new ArrayList<>();
		// 1. run uppaal if necessary
		if ((fileTrace == null) || fileTrace.isEmpty())
		{
			UppaalApi uppaal = new UppaalApi();
			fileTrace = uppaal.createCounterexample(fileModel);
			if ((fileTrace == null) || fileTrace.isEmpty() || !!!ResourceFile.exists(fileTrace))
			{
				System.out.println("Missing counterexample trace file.");
				return end(false);
			}
		}

		EventLog evS = eventLogger.logEvent("startDiagnosis");
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
				System.out.println("Run QE failed");
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
		} else if (use_state_qe)
		{
			z3RepairFile = createFileQEState();
			if (z3RepairFile == null)
				return end(false);

			// check interpolation
			return end(true);
		} else if (use_interpol)
		{
			List<String> inputList = getTestInputParameters();
			inputList.add(0, "-interpol");
			// inputList.add(0, "-dp");
			// inputList.add(1, "-" + SMT2_OPTION.getName(option));
			Ut2Smt2 converter = new Ut2Smt2();
			converter.parseArgument((String[]) inputList.toArray(new String[inputList.size()]));
			if (!!!converter.convert())
			{
				System.out.println("Conversion with interpol file failed.");
				return end(false);
			}
			modTraceFile = converter.getDestinyFile();
			return true;
		} else if (use_func)
		{
			// 2. parse counterexample trace and model and add modification of
			// trace
			if (!!!createFilesModifiedTracesFunc())
				return end(false);

			// 3. combine quantifier func trace and modified trace
			z3RepairFile = modTraceFile.replace(".smt2", "_diag.smt2");
			addExists_Func(modTraceFile, z3RepairFile);
		} else
		{
			// 2. parse counterexample trace and model and add modification of
			// trace
			if (!!!createFilesModifiedTracesImply())
				return end(false);

			// 3. combine quantifier func trace and modified trace
			z3RepairFile = modTraceFile;
			// diagFile = modTraceFile.replace(".smt2", "_diag.smt2");
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
			Repair repair = checkAdmissible(fileModel, sol);

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

			if (fault != null)
				fault.addRepair(repair);

			// eventLogger.logEvent("Checked admissibility");
			eventLogger.logEvent("Modify file");
			eventLogger.logEvent("TTS " + EquivalenceCheck.timeSpace1 + "ms");
			eventLogger.logEvent("TTS " + EquivalenceCheck.timeSpace2 + "ms");

			// same solution found again
			if ((solLast != null) && solLast.contains(sol))
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
		EventLog evE = new EventLog("endDiagnosis");
		evE.addEventValue("", maxMem, "MB");
		eventLogger.logEvent(evE);
		eventLogger.end();
		if (fault != null)
		{
			fault.setMemory(maxMem);
			fault.setMemoryZ3(maxZ3);
			fault.setVarZ3(varCount);
			fault.setAssertZ3(assertCount);
			fault.setMaxTraceLength(lengthTrace);
		}
		String opt = SMT2_OPTION.getName(option);
		eventLogger.save2File(folderDestiny + "/" + modelName + "_diagnostic_" + opt + ".txt");
		return ret;
	}

	public EventLogger getLogger()
	{
		return eventLogger;
	}

	private boolean transform2Trace()
	{
		Ut2Smt2 converter = new Ut2Smt2();
		List<String> inputList = getTestInputParameters();
		inputList = getTestInputParameters();
		converter = new Ut2Smt2();
		converter.parseArgument((String[]) inputList.toArray(new String[inputList.size()]));
		if (!!!converter.convert())
		{
			System.out.println("Conversion with modifiaction failed.");
			return false;
		}
		property = converter.getProperty();
		modTraceFile = converter.getDestinyFile();
		return true;
	}

	private boolean createFilesModifiedTracesByQE()
	{
		List<String> inputList = getTestInputParameters();
		inputList.add(0, "-qe");
		inputList.add(0, "-dp");
		if (option != null)
			inputList.add(1, "-" + SMT2_OPTION.getName(option));
		Ut2Smt2 converter = new Ut2Smt2();
		converter.parseArgument((String[]) inputList.toArray(new String[inputList.size()]));
		if (!!!converter.convert())
		{
			System.out.println("Conversion with quantifier elimination failed.");
			return false;
		}
		lengthTrace = converter.getTraceLength();
		destinyFile = converter.getDestinyFile();

		inputList = getTestInputParameters();
		inputList.add(0, "-dp");
		inputList.add(1, "-" + SMT2_OPTION.getName(option));
		converter = new Ut2Smt2();
		converter.parseArgument((String[]) inputList.toArray(new String[inputList.size()]));
		if (!!!converter.convert())
		{
			System.out.println("Conversion with modifiaction failed.");
			return false;
		}
		property = converter.getProperty();
		modTraceFile = converter.getDestinyFile();
		return true;
	}

	private boolean createFilesModifiedTracesImply()
	{
		List<String> inputList = getTestInputParameters();
		Ut2Smt2 converter = new Ut2Smt2();

		inputList = getTestInputParameters();
		// inputList.add(0, "-dp");
		inputList.add(0, "-imply");
		inputList.add(1, "-" + SMT2_OPTION.getName(option));
		converter = new Ut2Smt2();
		converter.parseArgument((String[]) inputList.toArray(new String[inputList.size()]));
		if (!!!converter.convert())
		{
			System.out.println("Conversion with modifiaction failed.");
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
		// next lines is a test output for result of quantifier eliminination
		// String qeResultFile = modTraceFile.replace(".smt2",
		// "_qe_result.smt2");
		// try (PrintWriter out = new PrintWriter(qeResultFile))
		// {
		// out.println(qe_model);
		// out.close();
		// } catch (FileNotFoundException e)
		// {
		// }

		// todo: ugly way to get declaration of variables in from statement
		// original code for creation is in transformation
		// String fromDef = ResourceFile.readContent(qeFile);
		// fromDef = Helper.textDeleteUntil(fromDef, "exists");
		// fromDef = Helper.textDeleteFrom(fromDef, "(and");
		// String fromDef = "(" + Smt22TextElimination.VarDeclaration + ")";

		String diagFile = modTraceFile.replace(".smt2", "_diag.smt2");
		// if(1==1)
		// return diagFile;
		Helper.copyFile(modTraceFile, diagFile);

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

		/*
		 * if (qeTrace.contains("exists")) { // this condition seems to be old
		 * qeTrace = qeTrace.replace("exists", "forall"); qeTrace =
		 * qeTrace.replace("(and", "(=>\n  (and"); qeTrace =
		 * qeTrace.substring(0, qeTrace.length() - 1) + " " + notProp + "))"; }
		 * else { // qeTrace += "(assert " + qeTrace + ")"; // qeTrace =
		 * "\n(forall \n" + fromDef + "\n(=>\n (and\n" + qeTrace + // ")"; //
		 * qeTrace += " " + notProp + "))"; }
		 */

		/*
		 * Scanner scanner = new Scanner(qeTrace); String text = ""; while
		 * (scanner.hasNext("(let")) { String s = scanner.next("(let"); text +=
		 * "(assert " + s + "\n)"; } String s = scanner.next(); /* String old =
		 * qeTrace; String next = qeTrace; int index = qeTrace.indexOf("(let");
		 * while(index !=0) { }
		 */
		/*
		 * if (qeTrace.contains("let")) { String[] split =
		 * qeTrace.split("(\\(let)"); String text = ""; for (String s : split) {
		 * if (text.compareTo("\n ") == 0) continue; text += "(assert (let" + s
		 * + "\n)\n"; } }
		 */
		String text = "(assert (and  " + qeTrace + "))";

		// System.out.println(qeTrace);
		Helper.appendText2File(diagFile, text);
		// Helper.appendText2File(diagFile, "(assert " + property.getTextSmt2()
		// + ")");
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

	private boolean createFilesModifiedTracesFunc()
	{
		List<String> inputList = getTestInputParameters();
		inputList.add(0, "-func");
		inputList.add(0, "-dp");
		inputList.add(1, "-" + SMT2_OPTION.getName(option));
		Ut2Smt2 converter = new Ut2Smt2();
		converter.parseArgument((String[]) inputList.toArray(new String[inputList.size()]));
		if (!!!converter.convert())
		{
			System.out.println("Conversion with quantifier elimination failed.");
			return false;
		}
		modTraceFile = converter.getDestinyFile();
		return true;
	}

	private String createFileQEState()
	{
		String fileName = "test/" + getFilenameModel(fileTrace).replace(".smt2", "_qe_inter.smt2");
		Helper.deleteFile(fileName);

		String header = ";interpolant computation\n";
		header += ";sequence interpolants per state\n\n";
		header += "(set-option :print-success false)\n";
		header += "(set-option :produce-interpolants true)\n";
		header += "(set-logic QF_UFLRA)\n\n";
		String body = "";
		for (int i = 1; i <= 8; i++) // each state
		{
			header += "(declare-const _d" + i + " Real)\n";
			header += "(declare-const x" + i + " Real)\n";
			header += "(declare-const y" + i + " Real)\n";
			header += "(declare-const z" + i + " Real)\n\n";

			// create qe-file
			List<String> inputList = getTestInputParameters();
			inputList.add(0, "-stateqe" + i);
			// inputList.add(0, "-dp");
			// inputList.add(1, "-" + SMT2_OPTION.getName(option));
			Ut2Smt2 converter = new Ut2Smt2();
			converter.parseArgument((String[]) inputList.toArray(new String[inputList.size()]));
			if (!!!converter.convert())
			{
				System.out.println("Conversion with state quantifier elimination failed.");
				return null;
			}
			modTraceFile = converter.getDestinyFile();

			// do qe-elimination
			SMTCall z3 = createSMTSolver();
			if (!!!z3.runEliminationFile(modTraceFile))
				return null;

			String model = z3.getEliminatedModel().replace("\n", "\n    ");
			String text = "\n(assert \n(! (and\n    " + model;
			text += ")\n:named S" + i + " ) ; name and\n ) ;assert\n";
			// add result model to new file

			body += text;
		}

		body = replaceReal(body);
		String textCmd = "\n(check-sat)\n";
		textCmd += "(get-interpolants S1 S2 S3 S4 S5 S6 S7)\n";
		textCmd += "(exit)";
		Helper.appendText2File(fileName, header + body + textCmd);
		return fileName;
	}

	private String replaceReal(String body)
	{
		body = body.replace("(to_real 0)", "0.0");

		int index = body.indexOf("(to_real ");
		while (index != -1)
		{
			body = body.substring(0, index) + body.substring(index + 9);
			index = body.indexOf(")", index);
			if (index != -1)
				body = body.substring(0, index) + ".0" + body.substring(index + 1);
			index = body.indexOf("(to_real ");
		}
		return body;
	}

	public ProgramStatus getStatus()
	{
		return status;
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

	private SMTCall createSMTSolver()
	{
		if (solver == SMT2_SOLVER.Z3)
			return new Z3Call();
		if (solver == SMT2_SOLVER.JAVA_SMT_Z3)
			return new JavaSmtCall();
		return null;
	}
}
