package kn.uni.sen.joblibrary.tartar.job_repaircomputation;

import java.util.ArrayList;
import java.util.List;

import kn.uni.sen.joblibrary.tartar.admissibility.AdmissibilityCheck;
import kn.uni.sen.joblibrary.tartar.common.SMT2_OPTION;
import kn.uni.sen.joblibrary.tartar.common.TarTarConfiguration;
import kn.uni.sen.jobscheduler.common.impl.JobAbstract;
import kn.uni.sen.jobscheduler.common.model.JobEvent;
import kn.uni.sen.jobscheduler.common.model.JobResult;
import kn.uni.sen.jobscheduler.common.model.JobState;
import kn.uni.sen.jobscheduler.common.model.ResourceInterface;
import kn.uni.sen.jobscheduler.common.model.RunContext;
import kn.uni.sen.jobscheduler.common.resource.ResourceEnum;
import kn.uni.sen.jobscheduler.common.resource.ResourceFile;
import kn.uni.sen.jobscheduler.common.resource.ResourceInteger;
import kn.uni.sen.jobscheduler.common.resource.ResourceString;
import kn.uni.sen.jobscheduler.common.resource.ResourceTag;
import kn.uni.sen.jobscheduler.common.resource.ResourceType;
import kn.uni.sen.tartar.smtcall.Z3Call;

public class Job_RepairComputation extends JobAbstract
{
	public static final String PARAMETER = "Parameter";
	public static final String TRACE = "Trace";
	public static final String MODEL = "Model";
	public static final String TIMEOUT_Z3 = "TimeoutZ3";
	public static final String SMT2 = "SMT2";
	public static final String PROPERTY = "Property";
	public static final String REPAIR_KIND = "RepairKind";
	public static final String REPAIR = "Repair";

	List<Repair> repairList = new ArrayList<>();

	public Job_RepairComputation(RunContext father)
	{
		super(father);
		this.version = TarTarConfiguration.getVersion();

		createInputDescr(PARAMETER, ResourceType.ENUM);
		createInputDescr(TRACE, ResourceType.FILE);
		createInputDescr(MODEL, ResourceType.FILE).addTag(ResourceTag.NECESSARY);
		createInputDescr(TIMEOUT_Z3, ResourceType.INTEGER);
		createInputDescr(SMT2, ResourceType.FILE);
		createInputDescr(PROPERTY, ResourceType.STRING);
		createInputDescr(REPAIR_KIND, ResourceType.ENUM).addTag(ResourceTag.NECESSARY);

		createResultDescr(REPAIR, ResourceType.STRING);
	}

	public Job_RepairComputation()
	{
		this(null);
	}

	@Override
	public JobState task()
	{
		ResourceFile modelFile = getResourceWithType(MODEL, false);
		ResourceFile traceFile = getResourceWithType(TRACE, false);
		ResourceEnum repOpt = getResourceWithType(REPAIR_KIND, false);
		if ((modelFile == null) || (repOpt == null))
			return endError("Missing some input");

		ResourceString propRes = getResourceWithType(PROPERTY, false);
		if (propRes != null)
		{
			logEventStatus(JobEvent.WARNING, "Property name is not yet implemented");
		}

		ResourceInteger time = getResourceWithType(TIMEOUT_Z3, false);
		if (time != null)
		{
			int timeVal = time.getDataValue();
			if (timeVal > 0)
				Z3Call.timeout = timeVal * 1000;
		}

		boolean z3 = false;
		List<SMT2_OPTION> optList = new ArrayList<>();
		kn.uni.sen.jobscheduler.common.model.ResourceInterface p = getResourceWithType(PARAMETER, false);
		while (p != null)
		{
			if ((p != null) || (p instanceof ResourceEnum))
			{
				SMT2_OPTION opt = SMT2_OPTION.valueOf(((ResourceEnum) p).getData());
				if (opt == SMT2_OPTION.Z3)
					z3 = true;
				else
					optList.add(opt);
			}
			p = p.getNext();
		}

		SMT2_OPTION opt = SMT2_OPTION.valueOf(repOpt.getData());
		optList.add(opt);

		String model = modelFile.getData();
		String trace = traceFile != null ? traceFile.getData() : null;
		boolean good = true;
		for (SMT2_OPTION option : optList)
		{
			Diagnostic diagnostic = new Diagnostic(this);
			diagnostic.setFolder(getFolderText());
			diagnostic.setZ3(z3);
			diagnostic.setAdmChecker(new AdmissibilityCheck(this));
			good &= diagnostic.diagnostic(model, trace, option);
			repairList.addAll(diagnostic.getRepairList());
		}
		return end(good ? JobResult.OK : JobResult.ERROR);
		// return end(JobResult.OK);
	}

	@Override
	public ResourceInterface getResultResource(String name)
	{
		if (REPAIR.equals(name))
		{
			// todo: implement
			return null;
		}
		return super.getResultResource(name);
	}
}
