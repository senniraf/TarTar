package kn.uni.sen.tartar;

public interface ProgramEvent
{
	void changeStatus(ProgramStatus status);

	void changeValue(String result);
}
