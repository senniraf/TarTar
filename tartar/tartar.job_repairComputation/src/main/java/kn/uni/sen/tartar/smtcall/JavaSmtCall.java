package kn.uni.sen.tartar.smtcall;

import java.math.BigInteger;
import java.util.List;

import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;

import kn.uni.sen.joblibrary.tartar.convert.SMTContext;
import kn.uni.sen.joblibrary.tartar.job_repaircomputation.EventLogger;
import kn.uni.sen.jobscheduler.common.resource.ResourceFile;

import org.sosy_lab.java_smt.api.SolverException;

public class JavaSmtCall implements SMTCall
{
	SolverContext contextInterpol;
	SolverContext contextZ3;
	EventLogger logger;

	public JavaSmtCall()
	{
		contextInterpol = SMTContext.createContext(Solvers.SMTINTERPOL);
		// contextZ3 = createContext(Solvers.Z3);
	}

	@Override
	public void setEventLogger(EventLogger logger)
	{
		this.logger = logger;
	}

	@Override
	public boolean runEliminationFile(String destinyFile)
	{
		System.out.println(destinyFile);
		return false;
	}

	@Override
	public String getEliminatedModel()
	{
		return null;
	}

	void test() throws SolverException, InterruptedException
	{
		FormulaManager fmgr = contextInterpol.getFormulaManager();

		BooleanFormulaManager bmgr = fmgr.getBooleanFormulaManager();
		IntegerFormulaManager imgr = fmgr.getIntegerFormulaManager();

		IntegerFormula a = imgr.makeVariable("a"), b = imgr.makeVariable("b"), c = imgr.makeVariable("c");
		BooleanFormula constraint = bmgr.or(imgr.equal(imgr.add(a, b), c),
				imgr.equal(imgr.add(a, c), imgr.multiply(imgr.makeNumber(2), b)));

		try (ProverEnvironment prover = contextInterpol.newProverEnvironment(ProverOptions.GENERATE_MODELS))
		{
			prover.addConstraint(constraint);
			boolean isUnsat = prover.isUnsat();
			if (!isUnsat)
			{
				Model model = prover.getModel();
				BigInteger value = model.evaluate(a);
				System.out.println(value);
			}
		}
	}

	void testInterpolation() throws SolverException, InterruptedException
	{
		String diagFile = "example_interpol/db-new-int-v2.smt2";
		diagFile = "example_interpol/usage.smt2";
		FormulaManager fmgr = contextInterpol.getFormulaManager();

		String text = ResourceFile.parseFile(diagFile);
		if (text == null)
			return;
		// text = "(assert (! (> x y) :named IP_0))";
		fmgr.parse(text);

		BooleanFormulaManager bmgr = fmgr.getBooleanFormulaManager();
		IntegerFormulaManager imgr = fmgr.getIntegerFormulaManager();

		IntegerFormula a = imgr.makeVariable("a"), b = imgr.makeVariable("b"), c = imgr.makeVariable("c");
		BooleanFormula constraint = bmgr.or(imgr.equal(imgr.add(a, b), c),
				imgr.equal(imgr.add(a, c), imgr.multiply(imgr.makeNumber(2), b)));

		try (ProverEnvironment prover = contextInterpol.newProverEnvironment(ProverOptions.GENERATE_MODELS))
		{
			prover.addConstraint(constraint);
			boolean isUnsat = prover.isUnsat();
			if (!isUnsat)
			{
				Model model = prover.getModel();
				BigInteger value = model.evaluate(a);
				System.out.println(value);
			}
		}
	}

	@Override
	public ModelSolution runFileSoft(String diagFile, List<ModelSolution> solList)
	{
		// Assume we have a SolverContext instance.
		try
		{
			// test();
			testInterpolation();
		} catch (SolverException e)
		{
			e.printStackTrace();
		} catch (InterruptedException e)
		{
			e.printStackTrace();
		}

		System.out.println(contextZ3.getSolverName());
		OptimizationProverEnvironment env = contextZ3.newOptimizationProverEnvironment();
		try
		{
			env.getModel();
		} catch (SolverException e)
		{
			e.printStackTrace();
		}

		// diagFile = "test/db.o0-t1-y-X1trace_func_dp_bv.smt2";
		diagFile = "test/simple.smt2";
		// System.out.println(diagFile);
		String text = ResourceFile.parseFile(diagFile);
		FormulaManager man = contextZ3.getFormulaManager();
		/* BooleanFormula form2 = */ man.parse(text);

		for (String line : text.split("\\r?\\n"))
		{
			BooleanFormula form = man.parse(line);
			System.out.println(form.toString());
		}
		return null;
	}

	@Override
	public double getMemory()
	{
		return Double.NaN;
	}

	@Override
	public int getVarCount()
	{
		return -1;
	}

	@Override
	public int getAssertCount()
	{
		return -1;
	}

	@Override
	public long getTime()
	{
		return -1;
	}
}
