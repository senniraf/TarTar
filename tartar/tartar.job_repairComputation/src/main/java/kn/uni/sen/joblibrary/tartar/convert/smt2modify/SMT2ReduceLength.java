package kn.uni.sen.joblibrary.tartar.convert.smt2modify;

/**
 * Reduce the length of a trace to certain depth
 * 
 * @author Martin Koelbl
 */
public class SMT2ReduceLength extends Smt2Clone
{
	public SMT2ReduceLength(int difLength)
	{
		this.reduceLength = difLength;
	}
}
