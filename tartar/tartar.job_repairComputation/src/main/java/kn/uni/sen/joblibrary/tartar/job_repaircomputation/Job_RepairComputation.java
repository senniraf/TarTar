package kn.uni.sen.joblibrary.tartar.job_repaircomputation;

import java.util.ArrayList;
import java.util.List;

import kn.uni.sen.joblibrary.tartar.admissibility.AdmissibilityCheck;
import kn.uni.sen.joblibrary.tartar.common.SMT2_OPTION;
import kn.uni.sen.joblibrary.tartar.common.TarTarConfiguration;
import kn.uni.sen.jobscheduler.common.impl.JobAbstract;
import kn.uni.sen.jobscheduler.common.model.EventHandler;
import kn.uni.sen.jobscheduler.common.model.JobEvent;
import kn.uni.sen.jobscheduler.common.model.JobResult;
import kn.uni.sen.jobscheduler.common.model.JobState;
import kn.uni.sen.jobscheduler.common.resource.ResourceDescription;
import kn.uni.sen.jobscheduler.common.resource.ResourceEnum;
import kn.uni.sen.jobscheduler.common.resource.ResourceFile;
import kn.uni.sen.jobscheduler.common.resource.ResourceInteger;
import kn.uni.sen.jobscheduler.common.resource.ResourceInterface;
import kn.uni.sen.jobscheduler.common.resource.ResourceList;
import kn.uni.sen.jobscheduler.common.resource.ResourceString;
import kn.uni.sen.jobscheduler.common.resource.ResourceTag;
import kn.uni.sen.jobscheduler.common.resource.ResourceType;
import kn.uni.sen.tartar.smtcall.Z3Call;

public class Job_RepairComputation extends JobAbstract
{
	protected ResourceDescription descrPara = new ResourceDescription("ParameterList", ResourceType.LIST);
	{
		descrPara.addChildDescription(new ResourceDescription("Parameter", ResourceType.ENUM));
	}
	protected ResourceDescription descrTrace = new ResourceDescription("Trace", ResourceType.FILE);
	protected ResourceDescription descrModel = new ResourceDescription("Model", ResourceType.FILE);
	protected ResourceDescription descrTimeout = new ResourceDescription("TimeoutZ3", ResourceType.INTEGER);
	protected ResourceDescription descrSmt2 = new ResourceDescription("SMT2", ResourceType.FILE);
	protected ResourceDescription descrProp = new ResourceDescription("Property", ResourceType.STRING);
	protected ResourceDescription descrRep = new ResourceDescription("RepairKind", ResourceType.ENUM);

	protected ResourceDescription descrRepairList = new ResourceDescription("RepairList", ResourceType.LIST);
	{
		descrRepairList.addChildDescription(new ResourceDescription("Repair", ResourceType.STRING));
	}

	List<Repair> repairList = new ArrayList<>();

	public Job_RepairComputation(EventHandler father)
	{
		super(father);
		this.version = TarTarConfiguration.getVersion();

		this.addInputDescription(descrModel);
		this.addInputDescription(descrProp);
		descrModel.addTag(ResourceTag.NECESSARY);
		this.addInputDescription(descrSmt2);
		this.addInputDescription(descrTrace);
		this.addInputDescription(descrPara);
		this.addInputDescription(descrTimeout);
		this.addInputDescription(descrRep);
		//descrRep.addTag(ResourceTag.NECESSARY);

		this.addResultDescription(descrRepairList);
	}

	public Job_RepairComputation()
	{
		this(null);
	}

	@Override
	public JobState task()
	{
		ResourceFile modelFile = descrModel.getResourceWithType();
		ResourceFile traceFile = descrTrace.getResourceWithType();
		ResourceEnum repOpt = descrRep.getResourceWithType();
		if ((modelFile == null) || (repOpt == null))
			return endError("Missing some input");

		ResourceString propRes = descrProp.getResourceWithType();
		if (propRes != null)
		{
			jobContext.logEvent(JobEvent.WARNING, "Property name is not yet implemented");
		}

		ResourceInteger time = descrTimeout.getResourceWithType();
		if (time != null)
		{
			int timeVal = time.getDataValue();
			if (timeVal > 0)
				Z3Call.timeout = timeVal * 1000;
		}

		boolean z3 = false;
		List<SMT2_OPTION> optList = new ArrayList<>();
		ResourceList paraList = descrPara.getResourceWithType();
		if ((paraList != null) && (paraList instanceof ResourceList))
			for (ResourceInterface e : paraList.getList())
			{
				if ((e == null) || (e.getData() == null))
					continue;
				SMT2_OPTION opt = SMT2_OPTION.valueOf(e.getData());
				if (opt == SMT2_OPTION.Z3)
					z3 = true;
				else
					optList.add(opt);
			}

		SMT2_OPTION opt = SMT2_OPTION.valueOf(repOpt.getData());
		optList.add(opt);

		String model = modelFile.getData();
		String trace = traceFile != null ? traceFile.getData() : null;
		boolean good = true;
		for (SMT2_OPTION option : optList)
		{
			Diagnostic diagnostic = new Diagnostic(jobContext);
			diagnostic.setFolder(jobContext.getFolder());
			diagnostic.setZ3(z3);
			diagnostic.setAdmChecker(new AdmissibilityCheck(jobContext));
			good &= diagnostic.diagnostic(model, trace, option);
			repairList.addAll(diagnostic.getRepairList());
		}
		return end(good ? JobResult.OK : JobResult.ERROR);
		// return end(JobResult.OK);
	}

	@Override
	public ResourceInterface getResource(String name, boolean out)
	{
		return null;
	}
}
