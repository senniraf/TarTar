package kn.uni.sen.tartar.uppaal2smt2;

import kn.uni.sen.tartar.smtcall.Z3Call;

public class TestZ3
{
	static String fileModel = "example_z3/o0-t1-y-X1.trace_inv.smt2";
	static String fileModel2 = "example_z3/o0-t1-y-X1.new.smt2";
	static String fileModel3 = "example_z3/o0-t1-y-X1.trace_qe.smt2";

	public static void main(String args[])
	{
		Z3Call z3 = new Z3Call();
		z3.runFile(fileModel);
		z3.runFile(fileModel2);
	}
}
