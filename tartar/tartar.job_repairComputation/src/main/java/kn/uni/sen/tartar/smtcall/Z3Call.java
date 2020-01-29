package kn.uni.sen.tartar.smtcall;

import java.util.ArrayList;
import java.util.Date;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;

import com.microsoft.z3.Tactic;
import com.microsoft.z3.AST;
import com.microsoft.z3.ApplyResult;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.FuncDecl;
import com.microsoft.z3.Goal;
import com.microsoft.z3.Model;
import com.microsoft.z3.Optimize;
import com.microsoft.z3.Quantifier;
import com.microsoft.z3.RealExpr;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Statistics;
import com.microsoft.z3.Status;

import kn.uni.sen.joblibrary.tartar.job_repaircomputation.EventLogger;
import kn.uni.sen.jobscheduler.common.resource.ResourceFile;
import kn.uni.sen.jobscheduler.common.resource.ResourceString;

public class Z3Call implements SMTCall
{
	// Model modelSolution;
	String eliminatedModel = null;
	EventLogger logger;

	double memory = Double.NaN;
	int varCount = 0;
	int assertCount = 0;
	long timeDif = 0;
	public static int timeout = 0;

	/*
	 * public Model getModel() { return modelSolution; }
	 */

	@Override
	public void setEventLogger(EventLogger logger)
	{
		this.logger = logger;
	}

	private Context createContext()
	{
		HashMap<String, String> cfg = new HashMap<String, String>();
		cfg.put("model", "true");
		if (timeout >= 0)
		{
			cfg.put("timeout", "" + timeout);
		}
		Context ctx = new Context(cfg);
		return ctx;
	}

	public boolean example()
	{
		System.out.println("XOR - test start");
		Context ctx = createContext();
		BoolExpr x = ctx.mkBoolConst("x");
		BoolExpr y = ctx.mkBoolConst("y");
		BoolExpr x_xor_y = ctx.mkXor(x, y);

		Model m = check(ctx, x_xor_y, Status.SATISFIABLE);
		System.out.println(m);

		System.out.println("Interpretation of x: " + m.getConstInterp(x));
		System.out.println("Interpretation of y: " + m.getConstInterp(y));

		System.out.println("XOR - test end");
		return true;
	}

	static int count = 0;

	public boolean runFile(String modelFile)
	{
		// return true;
		Date before = new Date();

		// modelSolution = null;
		System.gc();
		try
		{
			Context ctx = createContext();

			BoolExpr[] a = ctx.parseSMTLIB2File(modelFile, null, null, null, null);
			Optimize solver = ctx.mkOptimize();
			solver.Add(a);

			// ctx.mkso
			// ArithExpr xr = ctx.mkIntConst("x1");
			// IntSort sort = ctx.
			// BoolExpr e = ctx.mkEq(xr, ctx.mkInt(1));
			// solver.AssertSoft(e, 1, "");

			/*
			 * solver.AssertSoft(ctx.parseSMTLIB2String("(= y true)", null,
			 * null, null, null), 1, null);
			 */
			//System.out.println(a.toString());
			// Status us = solver.Check();

			if (solver.Check() != Status.SATISFIABLE)
				return false;

			Model m = solver.getModel(); // check(ctx, a, Status.SATISFIABLE);
			if (m != null)
			{
				// modelSolution = m;
				// System.out.println("Satisfiable");
				// System.out.println(m.toString());
			} // else
				// System.out.println("Unsatisfiable");

			long t_diff = ((new Date()).getTime() - before.getTime()) / 1000;

			System.out.println("SMT2 file read time: " + t_diff + " sec");

		} catch (Exception ex)
		{
			System.out.println(ex.toString());
			return false;
		}

		long t_diff = ((new Date()).getTime() - before.getTime()) / 1000;
		System.out.println("SMT2 file test took " + t_diff + " sec");
		return true;
	}
	
	public Model checkSat(String modelFile)
	{
		System.gc();
		try
		{
			Context ctx = createContext();
			BoolExpr[] a = ctx.parseSMTLIB2File(modelFile, null, null, null, null);
			Optimize solver = ctx.mkOptimize();
			solver.Add(a);

			if (solver.Check() != Status.SATISFIABLE)
				return null;
			return solver.getModel();
		} catch (Exception ex)
		{
			System.out.println(ex.toString());
		}
		return null;
	}
	
	public Expr[] checkSatObjectives(String modelFile)
	{
		System.gc();
		try
		{
			Context ctx = createContext();
			BoolExpr[] a = ctx.parseSMTLIB2File(modelFile, null, null, null, null);
			Optimize solver = ctx.mkOptimize();
			solver.Add(a);

			if (solver.Check() != Status.SATISFIABLE)
				return null;
			return solver.getObjectives();
		} catch (Exception ex)
		{
			System.out.println(ex.toString());
		}
		return null;
	}

	public void checkMetaData(String z3Code)
	{
		int count = ResourceString.countOccurrences(z3Code, "assert");
		if (count > assertCount)
			assertCount = count;
		count = ResourceString.countOccurrences(z3Code, "Real"); // declare-const
		if (count > varCount)
			varCount = count;
	}

	public void checkStatistic(Statistics statistics, boolean start)
	{
		com.microsoft.z3.Statistics.Entry mem = statistics.get("memory");
		if (start)
			memory = mem.getDoubleValue();
		else
			memory = mem.getDoubleValue() - memory;

		// com.microsoft.z3.Statistics.Entry timeE = statistics.get("time");
		// if (timeE != null)
		// time = (long) (timeE.getDoubleValue() * 1000);
		// System.out.println(memory);

		// System.out.println(statics.getKeys());
		// for (com.microsoft.z3.Statistics.Entry entry :
		// statistics.getEntries())
		// {
		// logger.setMemory(event, mem);
		// //System.out.println(entry.toString());
		// }
	}

	public boolean runEliminationFile(String modelFile)
	{
		// modelFile = "test/Simply.smt2";
		this.timeDif = -1;
		long time = System.currentTimeMillis();
		// modelSolution = null;
		System.gc();
		Context ctx = null;
		try
		{
			ctx = createContext();

			Tactic tactic = ctx.andThen(ctx.mkTactic("simplify"), ctx.mkTactic("qe2"), ctx.mkTactic("simplify"),
					ctx.mkTactic("propagate-ineqs"), ctx.mkTactic("propagate-values"));
			if (timeout > 0)
				tactic = ctx.tryFor(tactic, timeout);
			checkStatistic(tactic.getSolver().getStatistics(), true);

			BoolExpr[] a = ctx.parseSMTLIB2File(modelFile, null, null, null, null);

			Goal g4 = ctx.mkGoal(true, false, false);
			g4.add(a);
			// simplifyTactic = ctx.mkTactic("ctx-solver-simplify");
			// Tactic tactic = ctx.andThen(ctx.mkTactic("qe2"),
			// ctx.mkTactic("simplify"));
			// simplify / ctx-solver-simplify
			// ctx.mkTactic("ctx-solver-simplify"),

			// Tactic tactic = ctx.mkTactic("qe2");
			ApplyResult ar = tactic.apply(g4);
			this.timeDif = System.currentTimeMillis() - time;
			if (ar.getNumSubgoals() == 0)
				return false;

			checkStatistic(tactic.getSolver().getStatistics(), false);
			// statics.getEntries();
			// Statistics statics = new Statistics(ctx, ctx.re);
			// IDecRefQueue<Statistics> x = ctx.getStatisticsDRQ();

			Goal[] goals = ar.getSubgoals();
			Goal subGoal = goals[0];
			if (subGoal.getDepth() == 1)
			{
				// all executions are true
				eliminatedModel = "true";
				return true;
			}
			// System.out.println("Depth: " + subGoal.getDepth());
			if (subGoal.getNumExprs() == 0)
			{
				// System.out.println("Warning: QE result is 'true'");
				eliminatedModel = "true";
				return true;
			}
			// System.out.println("" + subGoal.getFormulas()[0].toString());
			eliminatedModel = "";
			// for (int i = 0; i < subGoal.getNumExprs(); i++)
			BoolExpr[] list = subGoal.getFormulas();
			for (int i = 0; i < list.length; i++)
				eliminatedModel += list[i].toString() + "\n";
			// System.out.println(eliminatedModel);

		} catch (Exception ex)
		{
			String s = ex.getMessage();
			if (s.compareTo("canceled") == 0)
			{
				System.out.println("Warning: Probably QE timeout");
				return false;
			}

			System.out.println(ex.toString());
			return false;
		} finally
		{
			if (ctx != null)
				ctx.close();
		}
		return true;
	}

	/**
	 * Run Z3 API to find solution with soft assert
	 */
	public ModelSolution runFileSoft(String modelFile, List<ModelSolution> solList)
	{
		this.timeDif = 0;
		long time = System.currentTimeMillis();

		// modelFile = "test/soft.smt2";
		// modelSolution = null;
		System.gc();
		try
		{
			Context ctx = createContext();

			Optimize solver = ctx.mkOptimize();
			checkStatistic(solver.getStatistics(), true);
			String content = ResourceFile.parseFile(modelFile);
			String ig = "";
			for (ModelSolution sol : solList)
			{
				// content += "\n(assert (not " + sol.getAssertNotText() + "
				// ))";
				ig += "\n(assert " + sol.getAssertText() + ")";
			}
			content += ig;
			checkMetaData(content);

			solver.fromString(content);
			// System.out.println(content);
			Status status = solver.Check();
			if (status == Status.UNKNOWN)
			{
				System.out.println("Warning: sat timeout");
				return null;
			}

			Model m = solver.getModel(); // check(ctx, a, Status.SATISFIABLE);
			checkStatistic(solver.getStatistics(), false);
			if (m != null)
			{
				// modelSolution = m;
				// System.out.println("Satisfiable");
				// System.out.println(m.toString());

				// get all soft assert
				List<Modification> softList = getSoftAsserts(solver.toString());
				addUppaalIDtoValues(softList, content);
				// solver.
				ModelSolution sol = new ModelSolution();
				FuncDecl[] list = m.getConstDecls();
				for (FuncDecl f : list)
				{
					String valNew = m.getConstInterp(f).toString();
					// System.out.println(f + " " + valNew);
					if (valNew.compareTo("0") == 0)
						valNew = "0.0";
					String name = f.getName().toString();
					// System.out.println(f);
					for (Modification val : softList)
					{
						// System.out.println(val.name + " " +
						// val.valueDefault);
						if ((name.compareTo(val.name) == 0) && (valNew.compareTo(val.valueDefault) != 0))
						{
							val.setNewValue(valNew);
							sol.addChange(val);
						}
						// System.out.println(f.toString());
						// System.out.println(f.getName());
						// System.out.println(f.getRange());
						// System.out.println("" + m.getConstInterp(f));
					}
				}
				if (sol.getChangeList().isEmpty())
				{
					for (FuncDecl f : list)
					{
						String valNew = m.getConstInterp(f).toString();
						if (valNew.compareTo("0") == 0)
							valNew = "0.0";
						for (Modification val : softList)
						{
							if ((f.getName().toString().compareTo(val.name) == 0)
									&& (valNew.compareTo(val.valueDefault) != 0))
							{
								val.valueNew = valNew;
								sol.addChange(val);
							}
							// System.out.println(f.toString());
							// System.out.println(f.getName());
							// System.out.println(f.getRange());
							// System.out.println("" + m.getConstInterp(f));
						}
					}
				}
				if ((list.length != 0) && (sol.getChangeList().isEmpty()))
					System.out.println("Warning: Model found without repair");

				this.timeDif = System.currentTimeMillis() - time;
				return sol;
			}
		} catch (Exception ex)
		{
			System.out.println("Error: Search repair: " + ex.toString());
			return null;
		}
		return null;
	}

	/**
	 * Parse id and index of uppaal model constraint from comments in smt2 file
	 * 
	 * @param modVarList
	 * @param smt2Code
	 */
	private void addUppaalIDtoValues(List<Modification> modVarList, String smt2Code)
	{
		String[] lines = smt2Code.split(System.getProperty("line.separator"));
		for (String line : lines)
		{
			if (!!!line.startsWith("(declare-const"))
				continue;
			int index = line.indexOf(";");
			if (index < 0)
				continue;
			for (Modification v : modVarList)
			{
				if (line.contains(v.getName()))
				{
					String t = line.substring(index + 1);
					String[] l = t.split("_");
					try
					{
						int id = Integer.parseInt(l[0]);
						int index2 = 0;
						if (l.length >= 2)
							Integer.parseInt(l[1]);
						v.setID(id, index2);
					} catch (Exception ex)
					{
					}
				}
			}
		}
	}

	private List<Modification> getSoftAsserts(String text)
	{
		List<Modification> ret = new ArrayList<>();
		String[] lines = text.split(System.getProperty("line.separator"));
		for (String line : lines)
		{
			if (line.contains("assert-soft"))
			{

				int index = line.indexOf("soft");
				if (index == -1)
					continue;
				String val = line.substring(index + 4);
				index = val.indexOf(":");
				if (index == -1)
					index = line.lastIndexOf(")");
				val = val.substring(0, index);
				String val2 = val;

				// if soft-assert is integer then parser needs to be deleted
				if (val.contains("to_real"))
					val = val.replace("(to_real ", "").replace(")", "");

				// Context ctx = createContext();
				while (val.startsWith(" "))
					val = val.replaceFirst(" ", "");

				String[] part = val.split(" ");
				String value = part[2].replace(")", "").replace(" ", "");
				String name = part[1];

				// only add a modification variable a single time
				boolean found = false;
				for (Modification cv : ret)
					if (cv.getName().compareTo(name) == 0)
					{
						found = true;
						break;
					}
				if (found)
					continue;

				ret.add(new Modification(val2, name, part[2].replace(")", ""), value));
			}
		}
		return ret;
	}

	// function is not used
	void visit(Expr e)
	{
		if (e.isApp())
		{
			int num = e.getNumArgs();
			for (int i = 0; i < num; i++)
			{
				visit(e.getArgs()[i]);
			}
			// do something
			// Example: print the visited expression
			FuncDecl f = e.getFuncDecl();
			System.out.println("application of " + f.getName() + ": " + e + "\n");
		} else if (e.isQuantifier())
		{
			visit(((Quantifier) e).getBody());
			// do something
		} else
		{
			System.out.println("error");
		}
	}

	int getCount(BoolExpr a)
	{
		// Iterate over the formula.
		LinkedList<Expr> q = new LinkedList<Expr>();
		q.add(a);

		int cnt = 0;
		while (q.size() > 0)
		{
			AST cur = (AST) q.removeFirst();
			cnt++;

			if (cur.getClass() == BoolExpr.class)
			{
				if (!(cur.isVar()))
					for (Expr c : ((Expr) cur).getArgs())
						q.add(c);
			} else if (cur.getClass() == Expr.class)
			{
				if (!(cur.isVar()))
					for (Expr c : ((Expr) cur).getArgs())
						q.add(c);
			} else if (cur.getClass() == RealExpr.class)
			{
				if (!(cur.isVar()))
					for (Expr c : ((Expr) cur).getArgs())
						q.add(c);

			} else if (cur.getClass() == Quantifier.class)
			{
			}
		}
		// System.out.println(cnt + " ASTs");
		return cnt;
	}

	Model check(Context ctx, BoolExpr f, Status sat)
	{
		// Tactic tactic = ctx.mkTactic("ctx-solver-simplify");
		// ApplyResult ar = ApplyTactic(ctx, ctx.mkTactic("simplify"), f);

		// asks for unsat core extraction to be enabled (the second true) for
		// the goal g, but the propagate-ineqs tactic does not support that
		// feature, so it throws an exception.
		// Goal g = ctx.mkGoal(true, true, false);

		Solver s = ctx.mkSolver();
		s.add(f);
		if (s.check() != sat)
			return null;
		if (sat == Status.SATISFIABLE)
			return s.getModel();
		return null;
	}

	void getOptimizerAssertion()
	{
		/*
		 * Z3Object solver2 = solver; Field fA =
		 * Z3Object.class.getDeclaredField("m_n_obj"); fA.setAccessible(true);
		 * long al = (long) fA.getLong(solver2); fA =
		 * Context.class.getDeclaredField("m_ctx"); fA.setAccessible(true); long
		 * al2 = (long) fA.getLong(ctx);
		 * 
		 * long lAssert = Native.optimizeGetAssertions(al2, al); String text =
		 * Native.optimizeToString(al2, al);
		 * 
		 * ASTVector v = new ASTVector(ctx, lAssert); long t =
		 * Native.solverGetAssertions(al2, lAssert);
		 * 
		 */
	}

	public String getEliminatedModel()
	{
		return eliminatedModel;
	}

	@Override
	public double getMemory()
	{
		return memory;
	}

	@Override
	public int getVarCount()
	{
		return varCount;
	}

	@Override
	public int getAssertCount()
	{
		return assertCount;
	}

	@Override
	public long getTime()
	{
		return timeDif;
	}
}
