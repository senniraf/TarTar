package kn.uni.sen.joblibrary.tartar.convert;

import kn.uni.sen.joblibrary.tartar.common.SMT2_OPTION;
import kn.uni.sen.jobscheduler.common.impl.JobAbstract;
import kn.uni.sen.jobscheduler.common.model.EventHandler;
import kn.uni.sen.jobscheduler.common.model.JobResult;
import kn.uni.sen.jobscheduler.common.model.JobState;
import kn.uni.sen.jobscheduler.common.resource.ResourceDescription;
import kn.uni.sen.jobscheduler.common.resource.ResourceFile;
import kn.uni.sen.jobscheduler.common.resource.ResourceInterface;
import kn.uni.sen.jobscheduler.common.resource.ResourceList;
import kn.uni.sen.jobscheduler.common.resource.ResourceTag;
import kn.uni.sen.jobscheduler.common.resource.ResourceType;

public class Job_Uppaal2Smt2 extends JobAbstract
{
	protected ResourceDescription descrPara = new ResourceDescription("Parameter", ResourceType.LIST);
	{
		descrPara.addChildDescription(new ResourceDescription("Parameter", ResourceType.ENUM));
	}
	protected ResourceDescription descrTrace = new ResourceDescription("Trace", ResourceType.FILE);
	protected ResourceDescription descrModel = new ResourceDescription("Model", ResourceType.FILE);
	protected ResourceDescription descrSmt2 = new ResourceDescription("SMT2", ResourceType.FILE);

	protected ResourceDescription descrResultSmt2 = new ResourceDescription("SMT2", ResourceType.FILE);
	ResourceFile resultSMT2 = null;

	public Job_Uppaal2Smt2(EventHandler father)
	{
		super(father);
		this.version = "3.7.0";

		this.addInputDescription(descrPara);
		this.addInputDescription(descrTrace);
		this.addInputDescription(descrModel);
		descrModel.addTag(ResourceTag.NECESSARY);
		this.addInputDescription(descrSmt2);

		this.addResultDescription(descrResultSmt2);
	}

	public Ut2Smt2 createConverter()
	{
		ResourceFile model = descrModel.getResourceWithType();
		if (model == null)
			return null;

		String trace = null;
		ResourceFile resTrace = descrTrace.getResourceWithType();
		if (resTrace != null)
			trace = resTrace.getData();

		String destiny = null;
		ResourceFile resDest = descrSmt2.getResourceWithType();
		if (resDest != null)
			destiny = resDest.getData();

		Ut2Smt2 ut2Smt2 = new Ut2Smt2(trace, model.getData(), destiny, jobContext);

		ResourceInterface list = descrPara.getResource();
		if (list instanceof ResourceList)
			for (ResourceInterface e : ((ResourceList) list).getList())
			{
				if ((e == null) || (e.getData() == null))
					continue;
				SMT2_OPTION mode = SMT2_OPTION.valueOf(e.getData());
				ut2Smt2.setOption(mode);
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
	public ResourceInterface getResource(String name, boolean out)
	{
		if (name == null)
			return null;
		if (name.equals(descrResultSmt2.getName()))
		{
			return resultSMT2;
		}
		return null;
	}
}
