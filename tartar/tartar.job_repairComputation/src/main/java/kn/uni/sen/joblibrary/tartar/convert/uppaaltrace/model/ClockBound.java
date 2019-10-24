package kn.uni.sen.joblibrary.tartar.convert.uppaaltrace.model;

public class ClockBound
{
	Clock first;
	Clock second;
	String bound;
	String compare;

	public ClockBound(Clock clock1, Clock clock2, String bound, String compare)
	{
		this.first = clock1;
		this.second = clock2;
		this.bound = bound;
		this.compare = compare;
	}

	public Clock getFirst()
	{
		return first;
	}

	public Clock getSecond()
	{
		return second;
	}

	public String getCompare()
	{
		return compare;
	}

	public String getCompareNegated()
	{
		if (compare.compareTo(">=") == 0)
			return "<=";
		else if (compare.compareTo(">") == 0)
			return "<";
		else if (compare.compareTo("<") == 0)
			return ">";
		else if (compare.compareTo("<=") == 0)
			return ">=";
		else
			System.out.println("Warning: Negation of comparison unkown.");
		return "";
	}

	public String getBound()
	{
		return bound;
	}

	public String getBoundNegated()
	{
		return "" + (-Integer.parseInt(bound));
	}
}
