package kn.uni.sen.joblibrary.tartar.common;

public interface CheckAdmissibility
{
	ResultAdm checkEquivalence(String file1, String file2);

	long getTimeSpace1();

	long getTimeSpace2();

	double getMemory();

	double getMaxMemory();

	void checkMem(long val);
}
