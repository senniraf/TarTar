package kn.uni.sen.tartar;

import kn.uni.sen.tartar.admissible.Repair;
import kn.uni.sen.tartar.gui.MainGui;
import kn.uni.sen.tartar.smtcall.ModelSolution;
import kn.uni.sen.tartar.uppaal2smt2.SMT2_OPTION;
import kn.uni.sen.tartar.util.Helper;

/**
 * This class is the console program to call overall approach of diagnostic
 * traces
 * 
 * @author Martin Koelbl
 */

public class MainDiagnostic extends Diagnostic implements Job2
{
	public static final String version = "2.6.0";
	static boolean bShowHelp;

	ProgramEvent programEvent;

	ExperimentData expData = null;
	// is class used by experiment?
	boolean called = false;

	public MainDiagnostic(ExperimentData expData)
	{
		super();
		called = true;
	}

	public MainDiagnostic()
	{
		super();
	}

	public void setTraceFile(String fileTrace)
	{
		this.fileTrace = fileTrace;
	}

	public void setModelFile(String fileModel)
	{
		this.fileModel = fileModel;
	}

	public void setProgramEvent(ProgramEvent programEvent)
	{
		this.programEvent = programEvent;
	}

	@Override
	protected void setProgramStatus(ProgramStatus status)
	{
		super.setProgramStatus(status);
		if (programEvent != null)
			programEvent.changeStatus(status);
	}

	@Override
	protected Repair checkAdmissible(String file, ModelSolution sol)
	{
		Repair repair = super.checkAdmissible(file, sol);
		if (repair != null)
		{
			String val = repair.isAdmissible() ? "Admissible: " : "Inadmissible: ";
			val += sol.toText() + " " + repair.getModificationText();
			if (programEvent != null)
				programEvent.changeValue(val);
		}
		return repair;
	}

	public void setOption(SMT2_OPTION option)
	{
		if (option == null)
			return;
		if (option == SMT2_OPTION.UNKOWN)
			return;
		// todo: save all options as a list
		if (option == SMT2_OPTION.Z3)
		{
			optionZ3 = true;
			return;
		}
		if (option == SMT2_OPTION.ELIMINATION)
		{
			use_qe = true;
			return;
		}
		if (option == SMT2_OPTION.FUNCTION)
		{
			use_qe = false;
			return;
		}

		this.option = option;
		if (expData == null)
			expData = new ExperimentData(option);
		if ((!!!called) && (expData != null))
		{
			fault = expData.addFault(SMT2_OPTION.getName(option));
			expData.addSeedFault("");
		}
	}

	void setCommentDepth(int val)
	{
		if ((val < 0) || (val > 2))
			return;
		commentDepth = val;
	}

	void setFolder(String folderDestiny)
	{
		this.folderDestiny = folderDestiny;
	}

	public static void showHelp()
	{
		System.out.println("uppaal2smt2-diagnostic: Version " + version);
		System.out.println("(C)opyright: University of Konstanz");
		System.out.println("This software find potential faults in a timed automata.");
		System.out.println("usage: uppaal2smt2 modelfile.xml -t tracefile.xml");
		System.out.println("argument: -d --destiny folder for diagnostic");
		System.out.println("argument: -z3 directly requests z3 by api (not implemented)");

		System.out.println("argument: -dbm smt2 output by DBMs");
		System.out.println("argument: -bv --boundary checks of invariant/... boundaries");
		System.out.println("argument: -qe --elimination for calculating with quantifier elimination");
		System.out.println("argument: -func --function for calculating with function");

		System.out.println("argument: -cr --clockreset checks for wrong clock (none) reset");
		System.out.println("argument: -cf --clockreference checks for wrong clock reference");
		System.out.println("argument: -cc --comparison checks for wrong comparison operator");
		System.out.println("argument: -us --urgentstate check for wrong (none) urgent state");

		System.out.println("argument: -cx for how many comments should be output in smt2 (x:= 0|1|2");
	}

	public boolean parseArgument(String[] args)
	{
		int counter = 0;
		String last = "";
		// parse all arguments for software
		for (; (counter < args.length); counter++)
		{
			if (args[counter].startsWith("-"))
			{
				if ((args[counter].compareTo("-h") == 0) || (args[counter].compareToIgnoreCase("--help") == 0))
					bShowHelp = true;
				else if ((args[counter].compareTo("-t") == 0) || (args[counter].compareToIgnoreCase("--trace") == 0))
					last = "-t";
				else if ((args[counter].compareTo("-d") == 0))
					last = "-d";
				else if ((args[counter].compareTo("-" + SMT2_OPTION.boundary_name) == 0)
						|| (args[counter].compareToIgnoreCase("--boundary") == 0))
					setOption(SMT2_OPTION.BOUNDARY);
				else if ((args[counter].compareTo("-" + SMT2_OPTION.qe_name) == 0)
						|| (args[counter].compareToIgnoreCase("--elimination") == 0))
					setOption(SMT2_OPTION.ELIMINATION);
				else if ((args[counter].compareTo("-func") == 0)
						|| (args[counter].compareToIgnoreCase("--function") == 0))
					setOption(SMT2_OPTION.FUNCTION);
				else if ((args[counter].compareTo("-dbm") == 0) || (args[counter].compareToIgnoreCase("--dbm") == 0))
					setOption(SMT2_OPTION.DBM);
				else if ((args[counter].compareTo("-" + SMT2_OPTION.reset_name) == 0)
						|| (args[counter].compareToIgnoreCase("--clockreset") == 0))
					setOption(SMT2_OPTION.RESET);
				else if ((args[counter].compareTo("-" + SMT2_OPTION.reference_name) == 0)
						|| (args[counter].compareToIgnoreCase("--clockreference") == 0))
					setOption(SMT2_OPTION.REFERENCE);
				else if ((args[counter].compareTo("-" + SMT2_OPTION.urgent_name) == 0)
						|| (args[counter].compareToIgnoreCase("--urgentstate") == 0))
					setOption(SMT2_OPTION.URGENT);
				else if ((args[counter].compareTo("-" + SMT2_OPTION.operator_name) == 0)
						|| (args[counter].compareToIgnoreCase("--comparison") == 0))
					setOption(SMT2_OPTION.COMPARISON);
				else if (args[counter].startsWith("-c"))
				{
					int val = Integer.parseInt(args[counter].substring(2));
					setCommentDepth(val);
				} else if (args[counter].compareTo("-z3") == 0)
					setOption(SMT2_OPTION.Z3);
				else
				{
					System.out.println("Warning: Unkown parameter: " + args[counter]);
				}
				continue;
			}

			if (last.compareTo("") == 0)
			{
				setModelFile(args[counter]);
			} else if (last.compareTo("-t") == 0)
			{
				setTraceFile(args[counter]);
			} else if (last.compareTo("-d") == 0)
			{
				setFolder(args[counter]);
			}
			last = "";
		}
		return true;
	}

	boolean checkInput()
	{
		boolean b = true;
		if (use_uppaal)
		{
			if (!!!UppaalApi.checkVersion())
			{
				System.out.println("Error: Missing Uppaal 4.1.*");
				b = false;
			}
		}
		if (fileTrace.compareTo("") == 0)
		{
			if (use_uppaal && !!!UppaalApi.checkVersion())
			{
				b = false;
				System.out.println("Error: Trace file for conversion is missing.");
			} else if (!!!use_uppaal)
			{
				use_uppaal = true;
				System.out.println("Warning: Trace file for conversion is missing. -> use upaal");
			}
		}
		if ((fileModel.compareTo("") == 0) && (option != SMT2_OPTION.DBM))
		{
			System.out.println("Error: Model file for conversion is missing.");
			b = false;
		}
		return b;
	}

	boolean runDiagnostic(String[] args)
	{
		parseArgument(args);
		if (bShowHelp)
		{
			showHelp();
			return true;
		}

		if (!checkInput())
			return false;

		// do conversion
		boolean ret = diagnostic();
		if ((!!!called) && (expData != null))
		{
			String name = modelName;
			if (name == null)
				name = "";
			String file = folderDestiny + "/" + name + ".txt";
			Helper.writeText2File(file, "");
			expData.writeData(file);
		}
		return ret;
	}

	public static void main(String[] args)
	{
		if (args.length == 0)
		{
			MainGui.main(args);
			return;
		}
		MainDiagnostic d = new MainDiagnostic();
		if (d.runDiagnostic(args))
			System.out.println("Diagnostic is done!");
		else
			System.out.println("Diagnostic has some error!");
	}

	@Override
	public void start()
	{
		if (getStatus() != ProgramStatus.WAIT)
			return;
		diagnostic();
	}
}
