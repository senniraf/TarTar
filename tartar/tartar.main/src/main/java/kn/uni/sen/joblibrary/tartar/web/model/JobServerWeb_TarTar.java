package kn.uni.sen.joblibrary.tartar.web.model;

import kn.uni.sen.joblibrary.tartar.gui.JobServer_TarTar;
import kn.uni.sen.jobscheduler.common.resource.ResourceFolder;
import kn.uni.sen.jobscheduler.core.model.JobRun;

public class JobServerWeb_TarTar extends JobServer_TarTar
{
	@Override
	protected JobRun createJobRun(Integer id)
	{
		ResourceFolder fol = createSessionFolder("result");
		return new JobRunWeb_TarTar(id, getEventHandler(), fol);
	}
}
