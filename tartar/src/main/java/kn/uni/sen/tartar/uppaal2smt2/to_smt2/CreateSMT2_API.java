package kn.uni.sen.tartar.uppaal2smt2.to_smt2;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;

import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.RationalFormulaManager;
import org.sosy_lab.java_smt.api.SolverContext;

import kn.uni.sen.tartar.smtcall.JavaSmtCall;
import kn.uni.sen.tartar.uppaal2smt2.smt2.model.ConstantSmt2;
import kn.uni.sen.tartar.uppaal2smt2.smt2.model.ConstraintSmt2;
import kn.uni.sen.tartar.uppaal2smt2.smt2.model.FunctionSmt2;
import kn.uni.sen.tartar.uppaal2smt2.smt2.model.TextSmt2;
import kn.uni.sen.tartar.uppaal2smt2.smt2.model.VariableSmt2;

public class CreateSMT2_API implements CreateSMT2
{
	private final SolverContext context = JavaSmtCall.createContext(Solvers.Z3);
	FormulaManager formManager = context.getFormulaManager();
	OptimizationProverEnvironment prover = context.newOptimizationProverEnvironment();

	BooleanFormulaManager bMng;
	RationalFormulaManager rMng;
	IntegerFormulaManager iMng;

	ArrayList<String> varNameList = new ArrayList<>();
	HashMap<Integer, Formula> varHash = new HashMap<>();

	public CreateSMT2_API()
	{
		rMng = formManager.getRationalFormulaManager();
		bMng = formManager.getBooleanFormulaManager();
		iMng = formManager.getIntegerFormulaManager();
	}

	@Override
	public void addComment(int level, String comment)
	{
	}

	@Override
	public void addOption(String opt, String val)
	{
	}

	@Override
	public int startCommand(String cmd)
	{
		return 0;
	}

	@Override
	public void addCommandParameter(String par)
	{
	}

	@Override
	public void endCommand(int id)
	{
	}

	@Override
	public void createVariable(String name, String type)
	{
		Formula f = null;
		if (type.toLowerCase().compareTo("int") == 0)
			f = iMng.makeVariable(name);
		else if (type.toLowerCase().compareTo("real") == 0)
			f = rMng.makeVariable(name);
		else if (type.toLowerCase().compareTo("bool") == 0)
			f = bMng.makeVariable(name);

		varNameList.add(name);
		if (f != null)
			varHash.put(varNameList.size() - 1, f);
	}

	@Override
	public void createFunction(String name, String type, ConstraintSmt2 con)
	{

	}

	@Override
	public void addFormula(ConstraintSmt2 con)
	{
		makeFormula(con);
		// System.out.println(con.getTextSmt2());
		// System.out.println(f.toString());
	}

	@Override
	public void finish()
	{
	}

	@Override
	public void addNewLine()
	{
	}

	public Formula makeFormula(TextSmt2 con)
	{
		if (con.getTextSmt2() == null)
			return null;
		if ((con instanceof VariableSmt2) || (con instanceof ConstantSmt2))
		{
			for (int i = 0; i < varNameList.size(); i++)
			{
				if (con.getTextSmt2() == null)
					continue;
				if (varNameList.get(i).compareTo(con.getTextSmt2()) == 0)
					return varHash.get(i);
			}
		}
		if (con instanceof ConstantSmt2)
		{
			if (con.getTextSmt2().compareTo("true") == 0)
				return bMng.makeTrue();
			if (con.getTextSmt2().compareTo("false") == 0)
				return bMng.makeFalse();
			if (con.getTextSmt2().contains("."))
				return rMng.makeNumber(con.getTextSmt2());
			return iMng.makeNumber(con.getTextSmt2());
		}

		if (!!!(con instanceof ConstraintSmt2))
			return null;
		ConstraintSmt2 c = (ConstraintSmt2) con;
		ArrayList<Formula> fList = new ArrayList<>();
		for (int i = 0; i < c.getConSize(); i++)
		{
			Formula f = makeFormula(c.getCon(i));
			if (f != null)
			{
				fList.add(f);
			} else
			{
				System.out.println("Missing: " + c.getTextSmt2());
			}
		}
		String op = c.getOperator();
		if (fList.isEmpty())
			return null;
		Formula first = fList.get(0);
		Formula second = null;
		if (fList.size() > 1)
			second = fList.get(1);

		if (op.compareTo("exists") == 0)
		{

		} else if (op.compareTo("forall") == 0)
		{

		} else if (first instanceof BooleanFormula)
		{
			if (op.compareTo("and") == 0)
				return bMng.and(getBoolList(fList));
			if (op.compareTo("or") == 0)
				return bMng.or(getBoolList(fList));
			if (op.compareTo("!") == 0)
				return bMng.not((BooleanFormula) fList.get(0));
			if (op.compareTo("=") == 0)
				return bMng.equivalence((BooleanFormula) fList.get(0), (BooleanFormula) fList.get(1));
			if (op.compareTo("=>") == 0)
				return bMng.implication((BooleanFormula) fList.get(0), (BooleanFormula) fList.get(1));
		} else if ((second != null) && ((first instanceof RationalFormula) || (second instanceof RationalFormula)))
		{
			NumeralFormula i1 = (NumeralFormula) fList.get(0);
			NumeralFormula i2 = (NumeralFormula) fList.get(1);
			if (op.compareTo("+") == 0)
				return rMng.add(i1, i2);
			if (op.compareTo("-") == 0)
				return rMng.subtract(i1, i2);
			if (op.compareTo("*") == 0)
				return rMng.multiply(i1, i2);
			if (op.compareTo("/") == 0)
				return rMng.divide(i1, i2);
			if (op.compareTo("=") == 0)
				return rMng.equal(i1, i2);
			if (op.compareTo("%") == 0)
				return rMng.modulo(i1, i2);
			if (op.compareTo("<=") == 0)
				return rMng.lessOrEquals(i1, i2);
			if (op.compareTo("<") == 0)
				return rMng.lessThan(i1, i2);
			if (op.compareTo(">=") == 0)
				return rMng.greaterOrEquals(i1, i2);
			if (op.compareTo(">") == 0)
				return rMng.greaterThan(i1, i2);
		} else if (first instanceof IntegerFormula)
		{
			IntegerFormula i1 = (IntegerFormula) fList.get(0);
			IntegerFormula i2 = (IntegerFormula) fList.get(1);
			if (op.compareTo("+") == 0)
				return iMng.add(i1, i2);
			if (op.compareTo("-") == 0)
				return iMng.subtract(i1, i2);
			if (op.compareTo("*") == 0)
				return iMng.multiply(i1, i2);
			if (op.compareTo("/") == 0)
				return iMng.divide(i1, i2);
			if (op.compareTo("=") == 0)
				return iMng.equal(i1, i2);
			if (op.compareTo("%") == 0)
				return iMng.modulo(i1, i2);
			if (op.compareTo("<=") == 0)
				return iMng.lessOrEquals(i1, i2);
			if (op.compareTo("<") == 0)
				return iMng.lessThan(i1, i2);
			if (op.compareTo(">=") == 0)
				return iMng.greaterOrEquals(i1, i2);
			if (op.compareTo(">") == 0)
				return iMng.greaterThan(i1, i2);
		}
		System.out.println("Error: Unkown operator " + op);
		return null;
	}

	Collection<BooleanFormula> getBoolList(List<Formula> fList)
	{
		Collection<BooleanFormula> list = new ArrayList<>();
		for (Formula f : fList)
			list.add((BooleanFormula) f);
		return list;
	}

	Collection<IntegerFormula> getIntList(List<Formula> fList)
	{
		Collection<IntegerFormula> list = new ArrayList<>();
		for (Formula f : fList)
			list.add((IntegerFormula) f);
		return list;
	}

	Collection<RationalFormula> getRealList(List<Formula> fList)
	{
		Collection<RationalFormula> list = new ArrayList<>();
		for (Formula f : fList)
			list.add((RationalFormula) f);
		return list;
	}

	@Override
	public void addFunction(FunctionSmt2 func)
	{
		// TODO Auto-generated method stub
	}
}
