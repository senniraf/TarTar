package kn.uni.sen.tartar.uppaal2smt2;

import java.util.ArrayList;
import java.util.EnumSet;

public enum SMT2_OPTION
{
	UNKOWN, Z3, DBM, BOUNDARY, ELIMINATION, REFERENCE, RESET, COMPARISON, URGENT, DEL_PROP, FUNCTION, STATE_ELIMINATION, IMPLY, INTERPOLATION;

	public final static String boundary_name = "bv";
	public final static String operator_name = "ov";
	public final static String reference_name = "cv";
	public final static String reset_name = "rv";
	public final static String urgent_name = "uv";
	public final static String deleteProp = "dp";
	public final static String negateProp = "np";
	public final static String qe_name = "qe";

	public static SMT2_OPTION[] ListModifier = new SMT2_OPTION[] { SMT2_OPTION.BOUNDARY, SMT2_OPTION.COMPARISON,
			SMT2_OPTION.REFERENCE, SMT2_OPTION.RESET, SMT2_OPTION.URGENT };

	public static String getName(SMT2_OPTION opt)
	{
		if (opt == null)
			return "missing";
		switch (opt)
		{
		case Z3:
			return "Z3";
		case DBM:
			return "dbm";
		case BOUNDARY:
			return boundary_name;
		case ELIMINATION:
			return qe_name;
		case REFERENCE:
			return reference_name;
		case RESET:
			return reset_name;
		case COMPARISON:
			return operator_name;
		case URGENT:
			return urgent_name;
		case IMPLY:
			return "imply";
		case DEL_PROP:
			return deleteProp;
		case FUNCTION:
			return "FUNC";
		case UNKOWN:
		default:
			break;
		}
		return "unkown";
	}

	public static String getLongName(SMT2_OPTION opt)
	{
		switch (opt)
		{
		case Z3:
			return "Z3";
		case DBM:
			return "dbm";
		case BOUNDARY:
			return "Boundary";
		case ELIMINATION:
			return "Quantifier Elimination";
		case REFERENCE:
			return "Clock Reference";
		case RESET:
			return "Clock Reset";
		case COMPARISON:
			return "Comparison";
		case URGENT:
			return "Urgent State";
		case IMPLY:
			return "Imply";
		case DEL_PROP:
			return "Negate Property";
		case FUNCTION:
			return "Function";
		case UNKOWN:
		default:
			break;
		}
		return "unkown";
	}

	public static SMT2_OPTION getOption(String val)
	{
		for (SMT2_OPTION opt : new ArrayList<>(EnumSet.allOf(SMT2_OPTION.class)))
		{
			String name = getName(opt);
			if (name == null)
				continue;
			if (getName(opt).compareTo(val) == 0)
				return opt;
		}
		return UNKOWN;
	}
}
