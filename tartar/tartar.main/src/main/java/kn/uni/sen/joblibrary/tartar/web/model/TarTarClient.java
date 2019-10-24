package kn.uni.sen.joblibrary.tartar.web.model;

import kn.uni.sen.joblibrary.tartar.gui.AnalysisTarTarType;
import kn.uni.sen.joblibrary.tartar.job_repaircomputation.Job_RepairComputation;
import kn.uni.sen.joblibrary_tartar.job_experiment.Job_SeedExperiment;
import kn.uni.sen.jobscheduler.common.impl.JobDataResult;
import kn.uni.sen.jobscheduler.common.model.Job;
import kn.uni.sen.jobscheduler.common.model.JobContext;
import kn.uni.sen.jobscheduler.common.model.JobEvent;
import kn.uni.sen.jobscheduler.common.resource.ResourceDescription;

public class TarTarClient extends JobDataResult implements Runnable
{
	JobContext context = null;
	// BufferLogger logger = new BufferLogger();
	AnalysisTarTarType type;
	Job job = null;

	TarTarClient(JobContext context)
	{
		this.context = context;
	}

	public void setAnalysis(AnalysisTarTarType analysisType)
	{
		type = analysisType;
	}

	public void run()
	{
		if (type == AnalysisTarTarType.ANALYSIS_REPAIR)
			job = new Job_RepairComputation(context.handler());
		else if (type == AnalysisTarTarType.ANALYSIS_SEED_EXPERIMENT)
			job = new Job_SeedExperiment(context.handler());
		else
		{
			context.logEventStatus(JobEvent.ERROR, "Unkown analysis.");
			return;
		}
		for (ResourceDescription descr : job.getInputDescription())
			descr.setOwner(this);

		job.start();

		// String fol = context.getFolder();
		// ResourceFolder.getUniqueFolder(fol+"")
		// ResourceFolder folder = new ResourceFolder();
		// jobClient.setResource("Folder", folder);
	}
}
