package kn.uni.sen.joblibrary.tartar.convert;

import kn.uni.sen.joblibrary.tartar.common.SMT2_OPTION;
import kn.uni.sen.jobscheduler.common.impl.JobAbstract;
import kn.uni.sen.jobscheduler.common.model.JobResult;
import kn.uni.sen.jobscheduler.common.model.JobState;
import kn.uni.sen.jobscheduler.common.model.ResourceInterface;
import kn.uni.sen.jobscheduler.common.model.RunContext;
import kn.uni.sen.jobscheduler.common.resource.ResourceEnum;
import kn.uni.sen.jobscheduler.common.resource.ResourceFile;
import kn.uni.sen.jobscheduler.common.resource.ResourceTag;
import kn.uni.sen.jobscheduler.common.resource.ResourceType;

public class Job_Uppaal2Smt2 extends JobAbstract
{
	public static final String PARAMETER = "Parameter";
	public static final String TRACE = "Trace";
	public static final String MODEL = "Model";
	public static final String SMT2 = "SMT2";

	ResourceFile resultSMT2 = null;

	public Job_Uppaal2Smt2(RunContext father)
	{
		super(father);
		this.version = "3.7.0";

		createInputDescr(PARAMETER, ResourceType.ENUM);
		createInputDescr(TRACE, ResourceType.FILE);
		createInputDescr(MODEL, ResourceType.FILE).addTag(ResourceTag.NECESSARY);
		createInputDescr(SMT2, ResourceType.FILE);

		createResultDescr(SMT2, ResourceType.FILE);
	}

	public Ut2Smt2 createConverter()
	{
		ResourceFile model = getResourceWithType(MODEL, false);
		if (model == null)
			return null;

		String trace = null;
		ResourceFile resTrace = getResourceWithType(TRACE, false);
		if (resTrace != null)
			trace = resTrace.getData();

		String destiny = null;
		ResourceFile resDest = getResourceWithType(SMT2, false);
		if (resDest != null)
			destiny = resDest.getData();

		Ut2Smt2 ut2Smt2 = new Ut2Smt2(trace, model.getData(), destiny, this);

		ResourceInterface p = getResourceWithType(PARAMETER, false);
		while (p != null)
		{
			if ((p != null) && (p instanceof ResourceEnum))
			{
				ResourceEnum para = (ResourceEnum) p;
				SMT2_OPTION mode = SMT2_OPTION.valueOf(para.getData());
				ut2Smt2.setOption(mode);
			}
			p = p.getNext();
		}
		return ut2Smt2;
	}

	@Override
	public JobState task()
	{
		Ut2Smt2 ut2Smt2 = createConverter();
		if (ut2Smt2 == null)
			return endError("Uppaal2SMT Converted was not created.");
		if (!!!ut2Smt2.convert())
			return endError("Conversion error");
		String dest = ut2Smt2.getDestinyFile();
		if ((dest != null) && (!!!dest.isEmpty()))
			resultSMT2 = new ResourceFile(dest);
		return end(JobResult.OK);
	}

	@Override
	public ResourceInterface getResultResource(String name)
	{
		if (name == null)
			return null;
		if (SMT2.equals(name))
		{
			return resultSMT2;
		}
		return super.getResultResource(name);
	}
}
