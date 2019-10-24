package kn.uni.sen.joblibrary.tartar.convert.to_smt2;

import kn.uni.sen.joblibrary.tartar.convert.smt2.model.ConstraintSmt2;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.FunctionSmt2;

/**
 * Interface to decide if writing model to file or to an api or ...
 * 
 * @author Martin Koelbl
 */
public interface CreateSMT2
{
	public void addComment(int level, String comment);

	public void addOption(String opt, String val);

	public int startCommand(String cmd);

	public void addCommandParameter(String par);

	public void endCommand(int id);

	public void createVariable(String name, String type);

	void createFunction(String name, String type, ConstraintSmt2 con);

	public void addFormula(ConstraintSmt2 con);
	
	public void addNewLine();

	/**
	 * Called at the end of traversing a model
	 */
	public void finish();

	public void addFunction(FunctionSmt2 func);
}
