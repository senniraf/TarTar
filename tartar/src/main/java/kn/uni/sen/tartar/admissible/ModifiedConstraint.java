package kn.uni.sen.tartar.admissible;

import kn.uni.sen.tartar.uppaal2smt2.SMT2_OPTION;

public class ModifiedConstraint
{
	SMT2_OPTION option;
	String modifyName;
	String org;
	String mod;

	public ModifiedConstraint(SMT2_OPTION o, String name, String org, String mod)
	{
		option = o;
		modifyName = name;
		this.org = org;
		this.mod = mod;
	}

	public SMT2_OPTION getOption()
	{
		return option;
	}

	public String getName()
	{
		return modifyName;
	}

	public String getOrginalConstraint()
	{
		return org;
	}

	public String getModifiedConstraint()
	{
		return mod;
	}
}
