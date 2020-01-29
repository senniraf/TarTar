package kn.uni.sen.joblibrary.tartar.job_tracecausality;

import kn.uni.sen.jobscheduler.common.helper.HelperConsole;
import kn.uni.sen.jobscheduler.common.impl.JobAbstract;
import kn.uni.sen.jobscheduler.common.model.JobEvent;
import kn.uni.sen.jobscheduler.common.model.JobResult;
import kn.uni.sen.jobscheduler.common.model.JobState;
import kn.uni.sen.jobscheduler.common.model.ResourceInterface;
import kn.uni.sen.jobscheduler.common.model.RunContext;
import kn.uni.sen.jobscheduler.common.resource.ResourceDouble;
import kn.uni.sen.jobscheduler.common.resource.ResourceFile;
import kn.uni.sen.jobscheduler.common.resource.ResourceFolder;
import kn.uni.sen.jobscheduler.common.resource.ResourceString;
import kn.uni.sen.jobscheduler.common.resource.ResourceTag;
import kn.uni.sen.jobscheduler.common.resource.ResourceType;
import kn.uni.sen.tartar.smtcall.Z3Call;

import java.time.Instant;
import java.time.temporal.ChronoUnit;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import kn.uni.sen.joblibrary.tartar.common.SMT2_OPTION;
import kn.uni.sen.joblibrary.tartar.common.uppaal.UppaalApi;
import kn.uni.sen.joblibrary.tartar.common.util.CheckJavaMemory;
import kn.uni.sen.joblibrary.tartar.convert.Ut2Smt2;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.ConstraintSmt2;
import kn.uni.sen.joblibrary.tartar.job_repaircomputation.Job_RepairComputation;

/**
 * Add different bugs to a model and try to find all of them.
 * 
 * @author Martin Koelbl
 */
public class Job_TraceCausality extends JobAbstract
{
	class CauseDelay
	{
		Set<String> DelaySet = null;;
		String Min = null;
		String Max = null;
	}

	List<CauseDelay> causeList = new ArrayList<>();
	CheckJavaMemory mem = new CheckJavaMemory();

	public static final String RES_CAUSE = "CAUSE";
	public static final String RES_MODEL = Job_RepairComputation.MODEL;
	public static final String RES_TRACE = Job_RepairComputation.TRACE;

	{
		createInputDescr(RES_MODEL, ResourceType.FILE).addTag(ResourceTag.NECESSARY);
		createInputDescr(RES_TRACE, ResourceType.FILE);
		createInputDescr(Job_RepairComputation.TIMEOUT_Z3, ResourceType.INTEGER);

		createResultDescr(RES_CAUSE, ResourceType.STRING);
	}

	public Job_TraceCausality(RunContext father)
	{
		super(father);
	}

	public Ut2Smt2 createConverter(String fileModel, String trace)
	{
		String modelName = ResourceFile.getFilenameOnly(fileModel);
		modelName += ".smt2";
		String destFile = ResourceFolder.appendFolder(getFolderText(), modelName);
		return new Ut2Smt2(trace, fileModel, destFile, this);
	}

	/**
	 * Checks if at least one realization of the trace satisfies the property.
	 * 
	 * @param mode
	 * @param trace
	 * @return null when a realization satisfy the property, otherwise empty
	 *         string or text with error
	 */
	Boolean checkAC2_1(String name, String trace, int len)
	{
		ResourceFile file = new ResourceFile(name + "AC21.z3");
		file.setFolder(getFolderText());

		file.removeFile();
		file.createFile(false);

		String clocks = "";
		String pos1 = "";
		for (int i = 1; i <= len + 1; i++)
		{
			clocks += "(declare-const _d" + i + " Real)\n";
			pos1 += "(>= _d" + i + " 0)\n";
		}

		String text = "";
		text += clocks + "\n";
		text += "\n" + allDef + "\n";
		text += "(assert(and\n " + pos1 + "))\n\n";
		text += "(assert (or (and\n";
		if (!!!prop.equals("false"))
			text += prop + "\n";
		text += trace + "\n";
		text += "\n";
		text += " (not(and\n";
		text += trace + "\n";
		text += ")))\n";

		file.appendText(text);
		// check sat
		Z3Call z3 = new Z3Call();
		boolean val = z3.checkSat(file.getData()) != null;
		mem.check(z3.getMemory());
		return val;
	}

	private boolean checkRange(int delayx, String name, String trace, int len)
	{
		String delay = "_d" + delayx;
		String delay2 = "_d" + delayx + "_2";
		ResourceFile file = new ResourceFile(name + "_range.z3");
		file.setFolder(getFolderText());

		String clocks = "";
		String pos1 = "";
		for (int i = 1; i <= len + 1; i++)
		{
			clocks += "(declare-const _d" + i + " Real)\n";
			pos1 += "(>= _d" + i + " 0)\n";
		}
		clocks += "(declare-const " + delay2 + " Real)\n";
		pos1 += "(>= " + delay2 + " 0)\n";

		String text = "";
		text += clocks + "\n";
		text += "\n" + allDef + "\n";
		text += "(assert (and\n " + pos1 + "))\n\n";
		text += "(assert (and (and\n";
		if (!!!prop.equals("false"))
			text += "(not " + prop + ")\n";
		text += trace + "\n";
		text += "\n";
		text += " (=>(and\n";
		trace = trace.replace(delay, delay2);
		text += trace + "\n";
		text += " " + prop + " \n";
		text += ");=>\n))\n";

		file.removeFile();
		file.createFile(false);
		file.appendText(text);

		Z3Call z3 = new Z3Call();
		boolean val = z3.checkSat(file.getData()) != null;
		mem.check(z3.getMemory());
		return val;
	}

	public static <T> Set<Set<T>> powerSet(Set<T> originalSet)
	{
		Set<Set<T>> sets = new LinkedHashSet<Set<T>>();
		if (originalSet.isEmpty())
		{
			sets.add(new HashSet<T>());
			return sets;
		}
		List<T> list = new ArrayList<T>(originalSet);
		T head = list.get(0);
		Set<T> rest = new LinkedHashSet<T>(list.subList(1, list.size()));
		for (Set<T> set : powerSet(rest))
		{
			Set<T> newSet = new HashSet<T>();
			newSet.add(head);
			newSet.addAll(set);
			sets.add(newSet);
			sets.add(set);
		}
		return sets;
	}

	private String createExtremCheck(boolean max, Set<String> dL, Set<String> ndL, String allText, int len)
	{
		String text = "";
		String pos1 = "";
		String clocks = "";
		String sum = "";
		for (int i = 1; i <= len + 1; i++)
		{
			pos1 += "(>= _d" + i + " 0)\n";
			clocks += "(_d" + i + " Real)";
		}

		for (String d : dL)
		{
			sum += " _" + d;
		}

		String start = "(declare-const min Real)\n";
		start += "(declare-const max Real)\n";
		start += "\n" + allDef + "\n";

		start += "(assert (<= min max))\n";
		start += "(assert (<= 0 min))\n";
		start += "(assert (<= 0 max))\n\n";

		text += start;

		text += "(assert \n";
		text += "(exists (" + clocks + ")\n";
		text += "(and (= min (+" + sum + "))\n";
		text += pos1;
		text += allText + "\n";
		text += "); exists min\n";
		text += "); assert\n\n";

		text += "(assert \n";
		text += "(exists (" + clocks + ")\n";
		text += "(and (= max (+" + sum + "))\n";
		text += pos1;
		text += allText + "\n";
		text += "); exists max\n";
		text += "); assert\n\n";

		text += "(assert\n";
		String forall = "(forall (" + clocks + ")\n";

		forall += "(=> ";
		forall += "(and (<= min (+" + sum + ")) (<= (+" + sum + ") max)\n";
		// forall += "(and\n";
		forall += pos1;
		forall += allText + "\n";
		// forall += "); trace and \n";
		forall += "(not " + prop + ")";
		forall += "); =>1\n";
		forall += "); forall\n";
		text += "(and \n";
		String qe = quantifierElimination(start, forall);
		if (qe == null)
			return null;
		text += qe;

		text += ")); assert\n";

		// text += "; get limits for property( maximize (+ d_i ...))\n";
		// text += "(" + maxText + " " + maxText.substring(0, 3) + ");\n";
		// text += "(apply ctx-solver-simplify)\n";
		text += "(set-option :opt.priority box)\n";
		text += "(minimize min)\n";
		text += "(maximize max)\n";
		// text += "(set-option:opt.priority box)\n";
		text += "(check-sat)\n";
		text += "(get-objectives)\n";

		return text;
	}

	String quantifierElimination(String begin, String forall)
	{
		// check if the left side of the intervall of min is the right one
		/*
		 * String extra = "assert (= min (+ 0.1 " + cause.Min + "))"; String
		 * code = ResourceFile.parseFile(file); code =
		 * code.replace("assert (<= 0 min)", extra); // code =
		 * code.replace("(set-option :opt.priority box)", "");
		 * ResourceFile.writeText2File(file, code);
		 * 
		 * String val2 = HelperConsole.runCommand("z3 " + file, null, true,
		 * 600); if (val2 == null || !!!val2.contains("unsat")) return null;
		 * 
		 * // code = ResourceFile.parseFile(file); String extra2 =
		 * "assert (>= min (+ 0.1 " + cause.Min + "))"; code =
		 * code.replace(extra, extra2); ResourceFile.writeText2File(file, code);
		 * 
		 * val2 = HelperConsole.runCommand("z3 " + file, null, true, 600); if
		 * (val2 == null || !!!val2.contains("unsat")) return val2; return null;
		 */
		String code = begin;
		code += "(assert " + forall + ")\n";
		code += "(apply (using-params qe ))";

		String file = ResourceFolder.appendFolder(getFolderText(), "check");
		file = ResourceFolder.appendFolder(file, "qe.z3");

		ResourceFile.createFile(file, true);
		ResourceFile.writeText2File(file, code);

		String val = HelperConsole.runCommand("z3 " + file, null, true, 600);
		if (val == null)
			return null;
		int start = val.indexOf("goal\n");
		if (start < 0)
			return null;
		start += 5;
		int end = val.indexOf(":precision");
		if (end < 0)
			return null;
		val = val.substring(start, end);
		return val;
	}

	private CauseDelay checkExtremValue(boolean max, Set<String> sL, Set<String> dL, String trace, String folder,
			int traceLength)
	{
		String name = "check"; // + (max ? "max" : "min");
		for (String d : sL)
			name += "_" + d;
		name += ".z3";
		String file = ResourceFolder.appendFolder(folder, name);
		ResourceFile.createFile(file, false);
		ResourceFile.appendText2File(file, createExtremCheck(max, sL, complement(dL, sL), trace, traceLength));

		// Z3Call z3 = new Z3Call();
		// Expr[] m = z3.checkSatObjectives("test.z3");

		// file = "test.z3";
		String val = HelperConsole.runCommand("z3 " + file, null, true, 600);
		mem.checkJavaMemory();
		// if(val.contains(""))
		// return null;
		if ((val == null) || val.contains("unsat") || val.contains("failed")
				|| (val.contains("error") && !!!val.contains("objectives")))
			return null;

		CauseDelay cause = new CauseDelay();
		cause.DelaySet = sL;
		cause.Min = parseValue(val, "min", true);

		if ("(* (- 1) oo)".equals(cause.Min))
			cause.Min = "0";
		cause.Max = parseValue(val, "max", false);
		if ("(* (- 1) oo)".equals(cause.Max))
			cause.Max = "oo";
		if ("1.0 (* (- 1.0) epsilon)".equals(cause.Max))
			cause.Max = "oo";

		// logMessage(JobEvent.INFO, cause.DelaySet + " (" + cause.Min + ",
		// " +
		// cause.Max + ")");
		if ((cause.Min == null) || (cause.Max == null))
			return null;
		return cause;
	}

	String[] getParts(String text)
	{
		List<String> part = new ArrayList<>();
		while (text.contains("  "))
			text = text.replace("  ", " ");
		while (text.startsWith(" "))
			text = text.substring(1);

		// System.out.println(text);
		byte[] bytes = text.getBytes();
		int last = 0;
		for (int i = 0; i < bytes.length; i++)
		{
			if (bytes[i] == ' ')
			{
				if (i != last)
					part.add(text.substring(last, i));
				last = i + 1;
			}
			if (bytes[i] == ')')
			{
				part.add(text.substring(last, i));
				last = i + 1;
				break;
			}
			if (bytes[i] == '(')
			{
				int n = text.lastIndexOf(" ", i);
				String t = getSubClose(text.substring(n + 1));
				part.add(t);
				i = n + t.length();
				last = i + 1;
			}
		}
		String end = text.substring(last);
		if (!!!end.isEmpty())
			part.add(end);
		// System.out.println(part);
		return part.toArray(new String[] {});
	}

	String getBracket(String val, String text)
	{
		int index = text.indexOf(val);
		if (index <= -1)
			return null;
		// index += par.length();
		String text2 = getSubClose(text.substring(index));
		return text2;
	}

	String parseValue(String res, String par, boolean first)
	{
		if ((res == null) || (par == null))
			return null;
		String text = getBracket(par, res);
		if (text == null)
			return null;

		String[] parts = getParts(text);
		if (parts[1].startsWith("(interval"))
		{
			parts = getParts(parts[1].substring(1, parts[1].length() - 1));
			if (first)
				parts[1] = parts[1];
			else
				parts[1] = parts[2];
		}
		if (parts[1].startsWith("(+"))
		{
			parts = getParts(parts[1].substring(1, parts[1].length() - 1));
			return parts[1];
		}
		return parts[1];
	}

	private String getSubClose(String con)
	{
		byte[] str = con.getBytes();
		int count = 0;
		for (int i = 0; i < str.length; i++)
		{
			byte val = str[i];
			if (val == ')')
			{
				count--;
				if (count <= 0)
					return con.substring(0, i + 1);
			}
			if (val == '(')
				count++;
			;
		}
		return "";
	}

	private Set<String> complement(Set<String> set, Set<String> subSet)
	{
		Set<String> cS = new HashSet<>();
		for (String s : set)
		{
			if (subSet.contains(s))
				continue;
			cS.add(s);
		}
		return cS;
	}

	int traceLength = -1;
	String prop = "false";

	private String createFileAll(String model, String trace)
	{
		Ut2Smt2 converter = createConverter(model, trace);
		// converter.setOption(SMT2_OPTION.DEL_PROP);
		converter.setOutput(SMT2_OPTION.ELIMINATION);
		if (!!!converter.convert())
		{
			logError("Error create forall file.");
			return null;
		}
		converter.getTraceLength();
		traceLength = converter.getTraceLength();
		ConstraintSmt2 con = converter.getProperty();
		if (con != null)
			prop = con.getTextSmt2();
		return converter.getDestinyFile();
	}

	String allDef = "";

	private String getSubString(String text, String from, String to)
	{
		int start = text.indexOf(from);
		if (start <= -1)
			return null;
		int end = text.indexOf(to, start);
		if (end <= -1)
			return null;
		end = text.lastIndexOf("\n", end);
		if (end <= -1)
			return null;

		return text.substring(start, end);
	}

	private String getSubLastString(String text, String from, String to)
	{
		int start = text.indexOf(from);
		if (start <= -1)
			return null;
		int end = text.lastIndexOf(to);
		if (end <= -1)
			return null;
		end = text.lastIndexOf("\n", end);
		if (end <= -1)
			return null;

		return text.substring(start, end);
	}

	private String getAllConstraint(String file)
	{
		String text = (new ResourceFile(file)).getContent();
		if (text == null)
		{
			logError("Missing pattern in z3 file");
			return null;
		}

		String val = getSubLastString(text, "; symbolic state 1", "; =>");

		String t = getSubString(text, "; declare local variables", "assert");
		String t2 = getSubString(text, "; declare local variables", "; define local variables");
		if (t == null)
			t = t2;
		else if ((t2 != null) && (t2.length() < t.length()))
			t = t2;

		if (t != null)
			allDef = t;

		t = getSubString(text, "; define local variables", "; delays are always positive");
		if ((t != null))
			allDef += "\n (assert(and " + t + "))";

		return val;
	}

	/**
	 * Computes all causes: for every subset s' of the power set of time delays
	 * s check AC2.2
	 * 
	 * @param mode
	 * @param trace
	 */
	void computeCauses(ResourceFile model, ResourceFile trace)
	{
		logMessage(JobEvent.INFO, "Model: " + model.getFilenameOnly());
		String folder = ResourceFolder.appendFolder(getFolderText(), "check");
		ResourceFolder.remove(folder);

		String name = model.getFilenameOnly();
		String fileSMT = createFileAll(model.getData(), trace.getData());
		String allText = getAllConstraint(fileSMT);

		// check AC2.1
		Boolean val = checkAC2_1(name, allText, traceLength);
		if (val == false)
		{
			logInfo("AC2.1 not fullfilled.");
			return;
		}

		// get set of delays
		// create power set of delays
		// powerSet
		Set<String> set = new LinkedHashSet<>();
		// for (int i = traceLength + 1; i >= 1; i--)
		for (int i = 1; i <= (traceLength + 1); i++)
			if (checkRange(i, name, allText, traceLength))
			{
				set.add("d" + i);
				System.out.print(" d" + i);
			}
		System.out.print("\n");
		Set<Set<String>> power = powerSet(set);

		// sort the sets, could be more efficient
		List<Set<String>> sets = sortSetByLength(power);

		for (Set<String> dL : sets)
		{
			if (dL.isEmpty())
				continue;
			// if (dL.size() >= 3)
			// continue;
			// todo:remove next line
			// if (dL.size() == set.size())
			// continue;
			CauseDelay cause = checkExtremValue(false, dL, set, allText, folder, traceLength);
			// System.out.println("" + dL);
			if (!!!((cause != null) && !!!("0".equals(cause.Min) && "oo".equals(cause.Max))))
				continue;
			if (!!!hasSubCause(cause, causeList))
			{
				causeList.add(cause);
				// logMessage(JobEvent.INFO, cause.DelaySet + " (" + cause.Min +
				// ", " + cause.Max + ")");
			}
		}

		// logMessage(JobEvent.INFO, "");
		deleteNonMinimalCauses(causeList);
		for (CauseDelay c2 : causeList)
			logMessage(JobEvent.INFO, c2.DelaySet + " (" + c2.Min + ", " + c2.Max + ")");

		Instant end = Instant.now();
		long dif = ChronoUnit.SECONDS.between(timeStart, end);
		long dif2 = ChronoUnit.MILLIS.between(timeStart, end) % 1000;
		logMessage(JobEvent.INFO, "time: " + dif + "s " + dif2 + "ms");
		logMessage(JobEvent.INFO, "memory: " + mem.getMaxMem() + "MB");

		timeEnd = Instant.now();
	}

	private List<Set<String>> sortSetByLength(Set<Set<String>> power)
	{
		List<Set<String>> sets = new ArrayList<>();
		for (Set<String> dL : power)
		{
			boolean f = false;
			for (int i = 0; i < sets.size(); i++)
				if (sets.get(i).size() >= dL.size())
				{
					sets.add(i, dL);
					f = true;
					break;
				}
			if (f == false)
				sets.add(dL);
		}
		return sets;
	}

	private boolean hasSubCause(CauseDelay c, List<CauseDelay> causeList2)
	{
		for (int i = 0; i < causeList.size(); i++)
		{
			CauseDelay c2 = causeList.get(i);
			// logMessage(JobEvent.INFO, c.DelaySet + " (" + c.Min + ", " +
			// c.Max + ")");
			// logMessage(JobEvent.INFO, c2.DelaySet + " (" + c2.Min + ", "
			// + c2.Max + ")");
			if (c == c2)
				return true;
			// check only truely smaller subset before
			if (!!!isSubset(c.DelaySet, c2.DelaySet))
				continue;
			// check range for every subset causeList
			if (!!!sameRange(c, c2))// && !!!combinedRange(c, causeList))
				continue;
			// logMessage(JobEvent.INFO, "[" + c.Min + "," + c.Max + "]" +
			// "[" + c2.Min + "," + c2.Max + "]");
			return true;
		}
		return false;
	}

	// todo:
	boolean combinedRange(CauseDelay cause, List<CauseDelay> causeList)
	{
		float min = 0;
		float max = 0;
		for (String d : cause.DelaySet)
		{
			for (CauseDelay c2 : causeList)
			{
				if ((c2.DelaySet.size() == 1) && c2.DelaySet.contains(d))
				{
					try
					{
						min += parseVal(c2.Min);
						float m = parseVal(c2.Max);
						if ((max == Float.POSITIVE_INFINITY) || (m == Float.POSITIVE_INFINITY))
						{
							max = Float.POSITIVE_INFINITY;
						} else
							max += m;
					} catch (Exception ex)
					{
						return false;
					}
				}
			}
		}
		try
		{
			Float min2 = Float.parseFloat(cause.Min);
			Float max2 = Float.parseFloat(cause.Max);
			if ((min == min2) && (max == max2))
				return true;
		} catch (Exception ex)
		{
		}
		return false;
	}

	boolean deleteNonMinimalCauses(List<CauseDelay> causeList2)
	{
		for (int j = causeList.size() - 1; j > 0; j--)
		{
			CauseDelay c = causeList.get(j);
			// remove all supersets with equal or bigger ranges
			// remove all supersets with constant range modification

			for (int i = 0; i < j && i < causeList.size(); i++)
			{
				CauseDelay c2 = causeList.get(i);
				// logMessage(JobEvent.INFO, c.DelaySet + " (" + c.Min + ", " +
				// c.Max + ")");
				// logMessage(JobEvent.INFO, c2.DelaySet + " (" + c2.Min + ", "
				// + c2.Max + ")");
				if (c == c2)
					break;
				// check only truely smaller subset before
				if (!!!isSubset(c.DelaySet, c2.DelaySet))
					continue;
				// check range for every subset causeList
				if (!!!sameRange(c, c2) && !!!combinedRange(c, causeList))
					continue;
				// logMessage(JobEvent.INFO, "[" + c.Min + "," + c.Max + "]" +
				// "[" + c2.Min + "," + c2.Max + "]");
				causeList.remove(j);
				break;
			}
		}
		return false;
	}

	private boolean sameRange(CauseDelay c, CauseDelay c2)
	{
		if ((c.Min == null) || (c.Max == null))
			return false;
		if (c.Min.equals(c2.Min) && c.Max.equals(c2.Max))
			return true;
		float min1 = parseVal(c.Min);
		float max1 = parseVal(c.Max);
		float min2 = parseVal(c2.Min);
		float max2 = parseVal(c2.Max);

		if ((min1 == min2) && (max1 == max2))
			return true;

		if ((max1 == Float.MAX_VALUE) && (max1 == max2))
			if (min1 == min2)
				return true;
			else
				return false;

		float dif1 = max1 - min1;
		float dif2 = max2 - min2;
		// if (dif1 == dif2)
		// return true;
		return false;
	}

	private float parseVal(String val)
	{
		if (val.equals("oo"))
			return Float.POSITIVE_INFINITY;
		if (val.equals("(* (- 1) oo)"))
			return Float.NEGATIVE_INFINITY;
		return Float.parseFloat(val);
	}

	private boolean isSubset(Set<String> set, Set<String> sub)
	{
		for (String s : sub)
		{
			boolean found = false;
			for (String s2 : set)
				if (s2 == s)
				{
					found = true;
					break;
				}
			if (!!!found)
			{
				// logMessage(JobEvent.INFO, "no : " + set + " " + sub);
				return false;
			}
		}
		// logMessage(JobEvent.INFO, "yes: " + set + " " + sub);
		return true;
	}

	@Override
	public JobState task()
	{
		ResourceFile model = getResourceWithType(RES_MODEL, false);

		// String folder = getFolderText();

		// parse timed counterexample
		// get delay set s
		ResourceFile trace = getResourceWithType(RES_TRACE, false);
		if (trace == null)
		{
			String trace2 = (new UppaalApi(this)).createCounterexample(model.getData());
			trace = new ResourceFile(trace2);
		}
		if ((trace == null) || !!!trace.exists())
		{
			return endError("Missing counterexample trace file.");
		}

		computeCauses(model, trace);

		// combine all causes

		return end(JobResult.OK);
	}

	@Override
	public ResourceInterface getResultResource(String name)
	{
		if (RES_CAUSE.equals(name))
		{
			ResourceString root = new ResourceString();
			int counter = 1;
			for (CauseDelay cd : causeList)
			{
				ResourceString cause = new ResourceString("Cause" + (counter++));
				ResourceString set = new ResourceString();
				set.setName("Set");
				for (String d : cd.DelaySet)
					if (d != null)
						set.addNext(new ResourceString(d));
				cause.addChild(set);

				ResourceDouble min = new ResourceDouble(Double.valueOf(cd.Min));
				min.setName("Minimum");
				cause.addChild(min);

				ResourceDouble max = new ResourceDouble(Double.valueOf(cd.Max));
				max.setName("Maximum");
				cause.addChild(max);
				root.addChild(cause);
			}
			return root;
		}
		return super.getResultResource(name);
	}
}
