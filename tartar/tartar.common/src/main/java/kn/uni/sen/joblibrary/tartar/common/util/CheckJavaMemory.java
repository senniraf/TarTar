package kn.uni.sen.joblibrary.tartar.common.util;

public class CheckJavaMemory
{
	Runtime instance = Runtime.getRuntime();
	double maxMem = 0.0;
	double mem = 0.0;

	public void reset()
	{
		mem = 0.0;
	}

	public void checkJavaMemory()
	{
		double mem2 = instance.totalMemory() - instance.freeMemory();
		mem2 /= (1024 * 1024);
		check(mem2);
	}

	public double getMem()
	{
		return mem;
	}

	public double getMaxMem()
	{
		return maxMem;
	}

	public void check(double mem2)
	{
		if (mem2 <= mem)
			return;
		mem = mem2;
		if (mem2 > maxMem)
			maxMem = mem2;
	}
}
