package kn.uni.sen.joblibrary.tartar.gui;

import kn.uni.sen.jobscheduler.common.resource.ResourceFolder;
import kn.uni.sen.jobscheduler.core.impl.JobServerAbstract;
import kn.uni.sen.jobscheduler.core.model.JobRun;
import kn.uni.sen.jobscheduler.core.model.JobSession;

public class JobServer_TarTar extends JobServerAbstract
{
	public JobServer_TarTar()
	{
		super("TarTar", "result");
	}

	public JobRun_TarTar createJobRun(Integer runID, RunParameter para)
	{
		JobRun run2 = super.createRun(runID);
		if (!!!(run2 instanceof JobRun_TarTar))
			return null;
		JobRun_TarTar run = (JobRun_TarTar) run2;
		run.setParameter(para);
		return run;
	}

	@Override
	protected JobRun createJobRun(Integer id)
	{
		ResourceFolder fol = createSessionFolder("result");
		return new JobRun_TarTar(id, getEventHandler(), fol);
	}

	@Override
	protected JobSession createSessionInstance(String user)
	{
		return null;
	}
}
