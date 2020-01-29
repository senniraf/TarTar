package kn.uni.sen.joblibrary.tartar.gui;

import kn.uni.sen.joblibrary.tartar.common.SMT2_OPTION;
import kn.uni.sen.joblibrary.tartar.job_repaircomputation.Job_RepairComputation;
import kn.uni.sen.joblibrary_tartar.job_experiment.Job_SeedExperiment;
import kn.uni.sen.jobscheduler.common.impl.JobDataInput;
import kn.uni.sen.jobscheduler.common.model.EventHandler;
import kn.uni.sen.jobscheduler.common.model.Job;
import kn.uni.sen.jobscheduler.common.model.ResourceInterface;
import kn.uni.sen.jobscheduler.common.resource.ResourceDescription;
import kn.uni.sen.jobscheduler.common.resource.ResourceEnum;
import kn.uni.sen.jobscheduler.common.resource.ResourceFile;
import kn.uni.sen.jobscheduler.common.resource.ResourceFileXml;
import kn.uni.sen.jobscheduler.common.resource.ResourceFolder;
import kn.uni.sen.jobscheduler.common.resource.ResourceList;
import kn.uni.sen.jobscheduler.core.impl.JobRunAbstract;
import kn.uni.sen.jobscheduler.core.model.JobScheduler;

public class JobRun_TarTar extends JobRunAbstract implements Runnable
{
	RunParameter Parameter;
	protected Job job = null;

	public JobRun_TarTar(Integer id, EventHandler father, ResourceFolder folder)
	{
		super(id, father, folder);
	}

	@Override
	public void run()
	{
		if (Parameter == null)
			return;
		if (Parameter.isExperiment())
			job = new Job_SeedExperiment(this);
		else
			job = new Job_RepairComputation(this);

		JobDataInput inData = new JobDataInput();
		//job.addLogger(new LogConsole(1));
		inData.add("Model", new ResourceFile(Parameter.getModelFile()));
		inData.add("Trace", new ResourceFile(Parameter.getTraceFile()));
		ResourceInterface para2 = null;
		for (SMT2_OPTION opt : Parameter.getOptionList())
			para2 = ResourceList.addList(para2, new ResourceEnum(opt));
		inData.add("Parameter", para2);
		inData.add("RepairKind", new ResourceEnum(Parameter.getRepair()));
		inData.add("SeedKind", new ResourceEnum(Parameter.getRepair()));

		ResourceDescription.setOwner(job.getInputDescription(), inData);
		if (job != null)
			job.start();
	}

	@Override
	protected JobScheduler createScheduler(ResourceFileXml jobFile, ResourceFolder folder, String schedulerType)
	{
		return null;
	}

	public void setParameter(RunParameter para)
	{
		Parameter = para;
	}
}
