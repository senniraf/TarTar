package kn.uni.sen.tartar.uppaal2smt2.smt2modify;

import java.util.List;

import kn.uni.sen.tartar.uppaal2smt2.SMT2_OPTION;
import kn.uni.sen.tartar.uppaal2smt2.smt2.model.ConstraintSmt2;
import kn.uni.sen.tartar.uppaal2smt2.smt2.model.ModelSmt2;
import kn.uni.sen.tartar.uppaal2smt2.smt2.model.TransitionSmt2;
import kn.uni.sen.tartar.uppaal2smt2.smt2.model.ConstraintSmt2.Design;

/**
 * Clone the current SMT2 model and negates the property
 * 
 * @author Martin Koelbl
 */
public class Smt2ModDeleteProp extends Smt2Clone
{
	public final static String bName = "_" + SMT2_OPTION.deleteProp;
	ConstraintSmt2 propConstraint;

	public Smt2ModDeleteProp()
	{
		dub.addStartComment("; delete property\n");
		dub.addFileExtra(bName);
	}

	@Override
	protected ModelSmt2 traverse(ModelSmt2 origin)
	{
		// do clone by traversing model
		super.traverse(origin);

		List<TransitionSmt2> list = dub.getTransitionList();
		if (list.isEmpty())
			return origin;

		TransitionSmt2 last = list.get(list.size() - 1);
		List<ConstraintSmt2> conList = last.getConstraintList();

		boolean found = true;
		// after each remove we have to restart the search as it is a
		// modification of the list
		while (found)
		{
			found = false;
			List<ConstraintSmt2> list2 = last.getConstraintList();
			for (ConstraintSmt2 con : list2)
			{
				// System.out.println(con.getTextSmt2());
				if (con.getDesign() != Design.GUARD)
					continue;
				found = true;
				propConstraint = con;
				propConstraint = computeProperty(propConstraint, origin.getCTLProperty());
				conList.remove(con);
				break;
			}
		}
		return origin;
	}

	private ConstraintSmt2 computeProperty(ConstraintSmt2 propConstraint2, ConstraintSmt2 constraintSmt2)
	{
		// todo: check if ctlProperty contains time constraint
		// else use propConstriant2
		if (constraintSmt2 != null)
			System.out.println(constraintSmt2.getTextSmt2());
		//System.out.println(propConstraint2.getTextSmt2());
		if (constraintSmt2 != null)
			return constraintSmt2;
		return propConstraint2;
	}

	public ConstraintSmt2 getProperty()
	{
		return propConstraint;
	}
}
