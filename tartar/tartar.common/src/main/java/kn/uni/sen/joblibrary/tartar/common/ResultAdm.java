package kn.uni.sen.joblibrary.tartar.common;

import java.util.List;

public class ResultAdm
{
	/**
	 * Counterexample for equivalence
	 */
	public List<String> trace;

	public boolean isAdmisible()
	{
		return trace == null;
	}
}
