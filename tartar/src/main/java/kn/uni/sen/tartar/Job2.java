package kn.uni.sen.tartar;

import kn.uni.sen.tartar.uppaal2smt2.SMT2_OPTION;

public interface Job2
{
	void start();

	void setModelFile(String modelFile);

	void setTraceFile(String traceFile);

	void setOption(SMT2_OPTION opt);

	void setProgramEvent(ProgramEvent programEvent);
}
