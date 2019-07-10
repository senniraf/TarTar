package kn.uni.sen.tartar.uppaal2smt2;

import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.PrintStream;

import kn.uni.sen.tartar.MainDiagnostic;
import kn.uni.sen.tartar.smtcall.Z3Call;
import kn.uni.sen.tartar.uppaal2smt2.Ut2Smt2;
import kn.uni.sen.tartar.uppaal2smt2.smt2.model.ConstraintSmt2;
import kn.uni.sen.tartar.uppaal2smt2.smt2.model.ModelSmt2;
import kn.uni.sen.tartar.uppaal2smt2.smt22file.Smt22Text;
import kn.uni.sen.tartar.uppaal2smt2.smt22file.Smt22TextElimination;
import kn.uni.sen.tartar.uppaal2smt2.smt22file.Smt22TextEliminationState;
import kn.uni.sen.tartar.uppaal2smt2.smt22file.Smt22TextFunctionImply;
import kn.uni.sen.tartar.uppaal2smt2.smt22file.Smt22TextImply;
import kn.uni.sen.tartar.uppaal2smt2.smt22file.Smt22TextInterpol;
import kn.uni.sen.tartar.uppaal2smt2.smt2modify.Smt2ModBoundary;
import kn.uni.sen.tartar.uppaal2smt2.smt2modify.Smt2ModComparison;
import kn.uni.sen.tartar.uppaal2smt2.smt2modify.Smt2ModDeleteProp;
import kn.uni.sen.tartar.uppaal2smt2.smt2modify.Smt2ModReference;
import kn.uni.sen.tartar.uppaal2smt2.smt2modify.Smt2ModReset;
import kn.uni.sen.tartar.uppaal2smt2.smt2modify.Smt2ModUrgent;
import kn.uni.sen.tartar.uppaal2smt2.uppaalmodel.model.Model;
import kn.uni.sen.tartar.uppaal2smt2.uppaaltrace.model.Trace;

/**
 * This class is the console program to call the class for parsing a
 * counterexample trace and a model, and modifying a counterexample trace
 * 
 * @author Martin Koelbl
 */
public class Ut2Smt2
{
	public static String version = MainDiagnostic.version;
	static boolean bShowHelp;
	static Ut2Smt2 ut2smt2;

	boolean optionZ3 = false;
	SMT2_OPTION optionOut;
	boolean optionDel;
	SMT2_OPTION option;
	String fileTrace = "";
	String fileModel = "";
	String fileDestiny = "";
	int commentDepth = 1;
	int state = 1;
	int lengthTrace = 0;
	int reduceLength = -1;

	// hack to get imply
	ConstraintSmt2 propConstraint;

	void setTraceFile(String fileTrace)
	{
		this.fileTrace = fileTrace;
	}

	void setModelFile(String fileModel)
	{
		this.fileModel = fileModel;
	}

	void setOption(SMT2_OPTION option)
	{
		// todo: save all options as a list
		if (option == SMT2_OPTION.Z3)
		{
			optionZ3 = true;
			return;
		}
		if (option == SMT2_OPTION.DEL_PROP)
		{
			optionDel = true;
			return;
		}
		this.option = option;
	}

	void setOutput(SMT2_OPTION option)
	{
		optionOut = option;
	}

	public String getDestinyFile()
	{
		return fileDestiny;
	}

	public int getTraceLength()
	{
		return lengthTrace;
	}

	protected boolean hasOption(SMT2_OPTION option)
	{
		if (option == SMT2_OPTION.Z3)
			return optionZ3;
		if (option == SMT2_OPTION.DEL_PROP)
			return optionDel;
		if (this.option == option)
			return true;
		return false;
	}

	void setCommentDepth(int val)
	{
		if ((val < 0) || (val > 2))
			return;
		commentDepth = val;
	}

	void setSMT2File(String fileDestiny)
	{
		this.fileDestiny = fileDestiny;
	}

	public boolean convert()
	{
		String text = "";
		String modelName = fileTrace;
		// 1. parse the original trace file
		Trace trace = new ParseUPPAAL<Trace>().parseFile(fileTrace, new Trace(modelName));
		if (trace == null)
		{
			System.out.println("Error, trace not parseable: " + fileTrace);
			return false;
		}
		lengthTrace = trace.getTraceLength();
		Trace2Smt2ByBDM transformer = null;
		Model model = null;
		// 2. Create converter
		if (option == SMT2_OPTION.DBM)
			transformer = new Trace2Smt2ByBDM();
		else
		{
			model = new ParseUPPAAL<Model>().parseFile(fileModel, new Model());
			transformer = new Trace2Smt2ByModel();
		}
		// 3. Combine uppaal trace and model into smt2 model
		ModelSmt2 smt2 = transformer.transform(trace, model, commentDepth);
		if (smt2 == null)
		{
			System.out.println("No model parsed!");
			return false;
		}

		ModelSmt2 smt2Modify = smt2;
		propConstraint = smt2Modify.getCTLProperty();
		if (model.hasErrorState() && optionDel && (propConstraint == null))
		{
			// 5. delete property of trace
			Smt2ModDeleteProp prop = new Smt2ModDeleteProp();
			smt2Modify = prop.createTrace(smt2Modify);
			// negate last transition guard
			propConstraint = negate(prop.getProperty());
		}
		// 6. Modify smt2 model
		if (option == SMT2_OPTION.BOUNDARY)
			smt2Modify = (new Smt2ModBoundary()).createTrace(smt2Modify);
		else if (option == SMT2_OPTION.URGENT)
			smt2Modify = (new Smt2ModUrgent()).createTrace(smt2Modify);
		else if (option == SMT2_OPTION.RESET)
			smt2Modify = (new Smt2ModReset()).createTrace(smt2Modify);
		else if (option == SMT2_OPTION.COMPARISON)
			smt2Modify = (new Smt2ModComparison()).createTrace(smt2Modify);
		else if (option == SMT2_OPTION.REFERENCE)
			smt2Modify = (new Smt2ModReference()).createTrace(smt2Modify);

		// todo: check if property has error states
		if (!!!model.hasErrorState() && optionDel && (propConstraint == null))
		{
			// 5. delete property of trace
			Smt2ModDeleteProp prop = new Smt2ModDeleteProp();
			smt2Modify = prop.createTrace(smt2Modify);
			// negate last transition guard
			propConstraint = negate(prop.getProperty());
		}

		// 7. Convert the smt2 model to text
		// (new TraverseSMT2(new CreateSMT2_File("test/text.smt2",
		// false))).transform(smt2Modify, 2);
		// (new TraverseSMT2(new CreateSMT2_API())).transform(smt2Modify, 2);

		boolean command = false;
		Smt22Text smt22Text = null;
		if (optionOut == SMT2_OPTION.ELIMINATION)
			smt22Text = new Smt22TextElimination(command, propConstraint, option);
		else if (optionOut == SMT2_OPTION.STATE_ELIMINATION)
			smt22Text = new Smt22TextEliminationState(false, state);
		else if (optionOut == SMT2_OPTION.INTERPOLATION)
			smt22Text = new Smt22TextInterpol(true);
		else if (optionOut == SMT2_OPTION.DBM)
			smt22Text = new Smt22Text(true, command);
		else if (optionOut == SMT2_OPTION.FUNCTION)
			smt22Text = new Smt22TextFunctionImply(command, propConstraint);
		else if (optionOut == SMT2_OPTION.IMPLY)
			smt22Text = new Smt22TextImply(command, propConstraint);
		else
			smt22Text = new Smt22Text(false, command);
		// smt22Text.setLogic("LRA");

		text = smt22Text.transform(smt2Modify, commentDepth);
		if (text == null)
			return false;

		// 8. write text to file
		if (fileDestiny.endsWith(".smt2"))
		{
			String fileEnd = smt22Text.getFileExtra() + smt2Modify.getFileExtra();
			fileDestiny = fileDestiny.replace(".smt2", fileEnd + ".smt2");
		}
		try (PrintStream out = new PrintStream(new FileOutputStream(fileDestiny)))
		{
			out.print(text);
		} catch (FileNotFoundException e)
		{
			e.printStackTrace();
		}

		// 9. run z3 solver if desired
		if (optionZ3)
		{
			Z3Call z3 = new Z3Call();
			return z3.runFile(fileDestiny);
		}

		return true;
	}

	private ConstraintSmt2 negate(ConstraintSmt2 property)
	{
		if (property == null)
			return property;
		ConstraintSmt2 not = new ConstraintSmt2("not");
		not.addCon(property);
		return not;
	}

	public ConstraintSmt2 getProperty()
	{
		return propConstraint;
	}

	boolean checkInput()
	{
		boolean b = true;
		if (fileTrace.compareTo("") == 0)
		{
			System.out.println("Error: Trace file for conversion is missing.");
			b = false;
		}
		if ((fileModel.compareTo("") == 0) && (option != SMT2_OPTION.DBM))
		{
			System.out.println("Error: Model file for conversion is missing.");
			b = false;
		}
		return b;
	}

	public static void showHelp()
	{
		System.out.println("uppaal2smt2: Version " + version);
		System.out.println("(C)opyright: University of Konstanz");
		System.out.println("This software converts a uppaal2 trace file to smt2 format.");
		System.out.println("usage: uppaal2smt2 tracefile.xml modelfile.xml destinyfile.smt2");
		System.out.println("argument: -dbm smt2 output by DBMs");
		System.out.println("argument: -b --boundary checks of invariant/... boundaries");
		System.out.println("argument: -qe --elimination for calculating with quantifier elimination");
		System.out.println("argument: -stateqe quantifier elimination in each state");

		System.out.println("argument: -cr --clockreset checks for wrong clock (none) reset");
		System.out.println("argument: -cf --clockreference checks for wrong clock reference");
		System.out.println("argument: -c --comparison checks for wrong comparison operator");
		System.out.println("argument: -us --urgentstate check for wrong (none) urgent state");

		System.out.println("argument: -cx for how many comments should be output in smt2 (x:= 0|1|2");
		System.out.println("argument: -z3 directly requests z3 by api (not implemented)");
	}

	public boolean parseArgument(String[] args)
	{
		int counter = 0;
		// parse all arguments for software
		for (; (counter < args.length) && args[counter].startsWith("-"); counter++)
		{
			if ((args[counter].compareTo("-h") == 0) || (args[counter].compareToIgnoreCase("--help") == 0))
				bShowHelp = true;
			else if ((args[counter].compareTo("-" + SMT2_OPTION.boundary_name) == 0)
					|| (args[counter].compareToIgnoreCase("--boundary") == 0))
				setOption(SMT2_OPTION.BOUNDARY);
			else if ((args[counter].compareTo("-" + SMT2_OPTION.qe_name) == 0)
					|| (args[counter].compareToIgnoreCase("--elimination") == 0))
				setOutput(SMT2_OPTION.ELIMINATION);
			else if (args[counter].compareTo("-interpol") == 0)
				setOutput(SMT2_OPTION.INTERPOLATION);
			else if (args[counter].compareTo("-imply") == 0)
				setOutput(SMT2_OPTION.IMPLY);
			else if (args[counter].startsWith("-stateqe"))
			{
				setOutput(SMT2_OPTION.STATE_ELIMINATION);
				state = Integer.parseInt(args[counter].replace("-stateqe", ""));
			} else if ((args[counter].compareTo("-func") == 0)
					|| (args[counter].compareToIgnoreCase("--function") == 0))
				setOutput(SMT2_OPTION.FUNCTION);
			else if ((args[counter].compareTo("-dbm") == 0) || (args[counter].compareToIgnoreCase("--dbm") == 0))
				setOutput(SMT2_OPTION.DBM);
			else if ((args[counter].compareTo("-" + SMT2_OPTION.reset_name) == 0)
					|| (args[counter].compareToIgnoreCase("--reset_variation") == 0))
				setOption(SMT2_OPTION.RESET);
			else if ((args[counter].compareTo("-" + SMT2_OPTION.reference_name) == 0)
					|| (args[counter].compareToIgnoreCase("--clockreference") == 0))
				setOption(SMT2_OPTION.REFERENCE);
			else if ((args[counter].compareTo("-" + SMT2_OPTION.urgent_name) == 0)
					|| (args[counter].compareToIgnoreCase("--urgent_variation") == 0))
				setOption(SMT2_OPTION.URGENT);
			else if ((args[counter].compareTo("-dp") == 0)
					|| (args[counter].compareToIgnoreCase("--delete_property") == 0))
				setOption(SMT2_OPTION.DEL_PROP);
			else if ((args[counter].compareTo("-" + SMT2_OPTION.operator_name) == 0)
					|| (args[counter].compareToIgnoreCase("--operator_variation") == 0))
				setOption(SMT2_OPTION.COMPARISON);
			else if (args[counter].startsWith("-c"))
			{
				// System.out.println(args[counter]);
				int val = parsePosInteger(args[counter].substring(2));
				if (val >= 0)
					setCommentDepth(val);
			} else if (args[counter].compareTo("-z3") == 0)
				setOption(SMT2_OPTION.Z3);
			else
			{
				System.out.println("Warning: Unkown parameter: " + args[counter]);
			}
		}

		// check for input and db file at least
		if (args.length - counter <= 1)
			return false;

		// get input file
		String fileTrace = args[counter];
		if (!fileTrace.endsWith(".xml"))
		{
			System.out.println("Warning: Source file has wrong extension.");
		}

		String fileModel = "";
		if (args.length - counter >= 2)
		{
			// destiny file is also given
			fileModel = args[counter + 1];
		}

		// get output file or use default
		String fileDestiny = "";
		if (args.length - counter >= 3)
		{
			// destiny file is also given
			fileDestiny = args[counter + 2];
		} else
		{
			// only one file is given -> replace extension of file (.xml) by
			// destiny file extension (.stm2)
			int index = fileTrace.lastIndexOf('.');
			if (index != -1)
				fileDestiny = fileTrace.substring(0, index);
			fileDestiny = fileDestiny + ".smt2";
		}

		setTraceFile(fileTrace);
		setModelFile(fileModel);
		setSMT2File(fileDestiny);
		return true;
	}

	private int parsePosInteger(String s)
	{
		int val = -1;
		try
		{
			val = Integer.parseInt(s);
		} catch (Exception ex)
		{
			return -1;
		}
		return val;
	}

	public static void main(String[] args)
	{
		ut2smt2 = new Ut2Smt2();
		ut2smt2.parseArgument(args);
		if (bShowHelp)
		{
			showHelp();
			return;
		}

		if (!ut2smt2.checkInput())
			return;

		// do conversion
		if (ut2smt2.convert())
			System.out.println("Transformation is done!");
		else
			System.out.println("Transformation has some error!");
	}
}
