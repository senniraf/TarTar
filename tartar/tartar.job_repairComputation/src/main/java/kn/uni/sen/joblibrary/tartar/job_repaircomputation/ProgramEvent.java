package kn.uni.sen.joblibrary.tartar.job_repaircomputation;

public interface ProgramEvent
{
	void changeStatus(ProgramStatus status);

	void changeValue(String result);
}
