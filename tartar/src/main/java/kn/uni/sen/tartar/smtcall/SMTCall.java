package kn.uni.sen.tartar.smtcall;

import java.util.List;

import kn.uni.sen.tartar.EventLogger;

public interface SMTCall
{
	void setEventLogger(EventLogger logger);

	boolean runEliminationFile(String destinyFile);

	String getEliminatedModel();

	ModelSolution runFileSoft(String diagFile, List<ModelSolution> solList);

	double getMemory();
	
	int getVarCount();

	int getAssertCount();
	
	long getTime();
}
