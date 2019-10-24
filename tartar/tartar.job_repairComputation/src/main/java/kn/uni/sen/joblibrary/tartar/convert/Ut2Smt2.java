package kn.uni.sen.joblibrary.tartar.convert;

import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.PrintStream;

import org.xml.sax.helpers.DefaultHandler;

import kn.uni.sen.joblibrary.tartar.common.SMT2_OPTION;
import kn.uni.sen.joblibrary.tartar.common.TarTarConfiguration;
import kn.uni.sen.joblibrary.tartar.convert.Ut2Smt2;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.ConstraintSmt2;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.ModelSmt2;
import kn.uni.sen.joblibrary.tartar.convert.smt22file.Smt22Text;
import kn.uni.sen.joblibrary.tartar.convert.smt22file.Smt22TextElimination;
import kn.uni.sen.joblibrary.tartar.convert.smt22file.Smt22TextEliminationState;
import kn.uni.sen.joblibrary.tartar.convert.smt22file.Smt22TextFunctionImply;
import kn.uni.sen.joblibrary.tartar.convert.smt22file.Smt22TextImply;
import kn.uni.sen.joblibrary.tartar.convert.smt22file.Smt22TextInterpol;
import kn.uni.sen.joblibrary.tartar.convert.smt22file.Smt22TextSingleAssert;
import kn.uni.sen.joblibrary.tartar.convert.smt2modify.Smt2ModBoundary;
import kn.uni.sen.joblibrary.tartar.convert.smt2modify.Smt2ModComparison;
import kn.uni.sen.joblibrary.tartar.convert.smt2modify.Smt2ModDeleteProp;
import kn.uni.sen.joblibrary.tartar.convert.smt2modify.Smt2ModReference;
import kn.uni.sen.joblibrary.tartar.convert.smt2modify.Smt2ModReset;
import kn.uni.sen.joblibrary.tartar.convert.smt2modify.Smt2ModUrgent;
import kn.uni.sen.joblibrary.tartar.convert.smt2modify.Smt2ModVarName;
import kn.uni.sen.joblibrary.tartar.convert.uppaalmodel.model.Model;
import kn.uni.sen.joblibrary.tartar.convert.uppaaltrace.model.Trace;
import kn.uni.sen.jobscheduler.common.model.JobContext;
import kn.uni.sen.jobscheduler.common.resource.ResourceFile;
import kn.uni.sen.jobscheduler.common.resource.ResourceFolder;

/**
 * This class is the console program to call the class for parsing a
 * counterexample trace and a model, and modifying a counterexample trace
 * 
 * @author Martin Koelbl
 */
public class Ut2Smt2
{
	public static String version = TarTarConfiguration.getVersion();
	static boolean bShowHelp;
	static Ut2Smt2 ut2smt2;

	boolean optionZ3 = false;
	SMT2_OPTION optionOut;
	boolean optionDel;
	SMT2_OPTION option;
	SMT2_OPTION option2 = SMT2_OPTION.UNKOWN;
	String fileTrace = "";
	String fileModel = "";
	String fileDestiny = null;
	int commentDepth = 1;
	int state = 1;
	int lengthTrace = 0;
	int reduceLength = -1;

	// hack to get imply
	ConstraintSmt2 propConstraint;

	JobContext jobContext;

	public Ut2Smt2(String trace, String model, String dest, JobContext context)
	{
		this.jobContext = context;
		fileTrace = trace;
		fileModel = model;
		fileDestiny = dest;
	}

	void setTraceFile(String fileTrace)
	{
		this.fileTrace = fileTrace;
	}

	void setModelFile(String fileModel)
	{
		this.fileModel = fileModel;
	}

	public void setOption(SMT2_OPTION option)
	{
		// todo: save all options as a list
		if (option == SMT2_OPTION.APPEND)
		{
			option2 = option;
			return;
		}
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

	public void setOutput(SMT2_OPTION option)
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
		Trace trace = new ParseUPPAAL<Trace>()
		{
			@Override
			protected DefaultHandler createHandler(Trace t)
			{
				return new UPPAALTraceHandler((Trace) t);
			}
		}.parseFile(fileTrace, new Trace(modelName));

		if ((fileDestiny == null) || (fileDestiny.isEmpty()))
			fileDestiny = createDestinyFile();

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
			transformer = new Trace2Smt2ByBDM(jobContext);
		else
		{
			model = (new ParseUPPAAL<Model>()
			{
				@Override
				protected DefaultHandler createHandler(Model m)
				{
					return new UPPAALModelHandler(m);
				}
			}).parseFile(fileModel, new Model());
			transformer = new Trace2Smt2ByModel(jobContext);
		}
		// 3. Combine uppaal trace and model into smt2 model
		ModelSmt2 smt2 = transformer.transform(trace, model);
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
			// 6.b delete property of trace
			Smt2ModDeleteProp prop = new Smt2ModDeleteProp();
			smt2Modify = prop.createTrace(smt2Modify);
			// negate last transition guard
			propConstraint = negate(prop.getProperty());
		}

		// 7. Convert the smt2 model to text
		// (new TraverseSMT2(new CreateSMT2_File("test/text.smt2",
		// false))).transform(smt2Modify, 2);
		// (new TraverseSMT2(new CreateSMT2_API())).transform(smt2Modify, 2);
		if (option2 == SMT2_OPTION.APPEND)
		{
			smt2Modify = (new Smt2ModVarName()).createTrace(smt2Modify, "alt");
		}

		boolean command = false;
		Smt22Text smt22Text = null;
		if (optionOut == SMT2_OPTION.ELIMINATION)
			smt22Text = new Smt22TextElimination(command, jobContext, propConstraint, option);
		else if (optionOut == SMT2_OPTION.STATE_ELIMINATION)
			smt22Text = new Smt22TextEliminationState(false, state, jobContext);
		else if (optionOut == SMT2_OPTION.INTERPOLATION)
			smt22Text = new Smt22TextInterpol(true, jobContext);
		else if (optionOut == SMT2_OPTION.DBM)
			smt22Text = new Smt22Text(true, command, jobContext);
		else if (optionOut == SMT2_OPTION.FUNCTION)
			smt22Text = new Smt22TextFunctionImply(command, propConstraint, jobContext);
		else if (optionOut == SMT2_OPTION.IMPLY)
			smt22Text = new Smt22TextImply(command, propConstraint, jobContext);
		else if (optionOut == SMT2_OPTION.SINGLE_ASSERT)
			smt22Text = new Smt22TextSingleAssert(command, propConstraint, jobContext);
		// else if (optionOut == SMT2_OPTION.ReplaceAll)
		// smt22Text = new Smt22TextReplaceAll(command, jobContext,
		// propConstraint, option);
		else
			smt22Text = new Smt22Text(false, command, jobContext);
		// smt22Text.setLogic("LRA");

		text = smt22Text.transform(smt2Modify);
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
			// todo: is this necessary?
			// Z3Call z3 = new Z3Call();
			// return z3.runFile(fileDestiny);
		}
		return true;
	}

	private String createDestinyFile()
	{
		String folder = jobContext.getFolder();
		String file = ResourceFile.getFilenameOnly(fileModel) + ".smt2";
		return ResourceFolder.appendFolder(folder, file);
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
}
