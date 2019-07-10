package kn.uni.sen.tartar.uppaal2smt2;

public class Transformer
{
	protected String fileExtra = "";
	protected String variant = "";
	protected int commentDepth = 2;

	protected final static String start = "; UPPAAL symbolic trace to smt2 translation (Version " + Ut2Smt2.version
			+ ")\n";
	public final static String t0Name = "_d";

	public String getVariant()
	{
		return variant;
	}

	public String getFileExtra()
	{
		return fileExtra;
	}

	public void setCommentDepth(int depth)
	{
		commentDepth = depth;
	}

	public String comment(int depth, String comment)
	{
		// commentDepth == 0 -> no comments
		// commentDepth == 1 -> state and transition names
		// commentDepth == 2 -> reason for properties
		// commentDepth == 3 -> original source text
		if ((depth > commentDepth) || (depth == 0))
			return "";
		return comment;
	}
	
	
	
	public void setFileExtra(String string)
	{
		fileExtra = string;	
	}
}
