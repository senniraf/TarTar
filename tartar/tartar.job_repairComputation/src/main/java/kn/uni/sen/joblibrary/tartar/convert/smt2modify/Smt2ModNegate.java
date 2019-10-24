package kn.uni.sen.joblibrary.tartar.convert.smt2modify;

import java.util.List;

import kn.uni.sen.joblibrary.tartar.common.SMT2_OPTION;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.ConstraintSmt2;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.ModelSmt2;
import kn.uni.sen.joblibrary.tartar.convert.smt2.model.TransitionSmt2;

/**
 * Clone the current SMT2 model and negates the property
 * 
 * @author Martin Koelbl
 */
public class Smt2ModNegate extends Smt2Clone
{
	public final static String bName = "_" + SMT2_OPTION.negateProp;

	public Smt2ModNegate()
	{
		dub.addStartComment("; negate property modification\n");
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
		boolean first = true;
		List<ConstraintSmt2> conList = last.getConstraintList();
		for (ConstraintSmt2 con : last.getConstraintList())
		{
			// todo: there could be not only one constraint
			if (!!!first)
				continue;
			first = false;
			ConstraintSmt2 not = new ConstraintSmt2("not", con);
			conList.remove(con);
			conList.add(not);
		}

		return origin;
	}
}
