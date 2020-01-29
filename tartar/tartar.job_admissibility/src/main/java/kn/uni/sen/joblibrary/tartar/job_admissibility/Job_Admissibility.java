package kn.uni.sen.joblibrary.tartar.job_admissibility;

import kn.uni.sen.joblibrary.tartar.admissibility.AdmissibilityCheck;
import kn.uni.sen.joblibrary.tartar.common.ResultAdm;
import kn.uni.sen.joblibrary.tartar.common.TarTarConfiguration;
import kn.uni.sen.jobscheduler.common.impl.JobAbstract;
import kn.uni.sen.jobscheduler.common.model.JobResult;
import kn.uni.sen.jobscheduler.common.model.JobState;
import kn.uni.sen.jobscheduler.common.model.ResourceInterface;
import kn.uni.sen.jobscheduler.common.model.RunContext;
import kn.uni.sen.jobscheduler.common.resource.ResourceBool;
import kn.uni.sen.jobscheduler.common.resource.ResourceFile;
import kn.uni.sen.jobscheduler.common.resource.ResourceTag;
import kn.uni.sen.jobscheduler.common.resource.ResourceType;

public class Job_Admissibility extends JobAbstract
{
	public static final String MODEL1 = "Model1";
	public static final String MODEL2 = "Model2";
	public static final String ADMISSIBLE = "Admissible";

	String fileModel1 = null;
	String fileModel2 = null;
	ResultAdm result = null;

	public Job_Admissibility(RunContext father)
	{
		super(father);
		this.version = TarTarConfiguration.getVersion();

		createInputDescr(MODEL1, ResourceType.FILE).addTag(ResourceTag.NECESSARY);
		createInputDescr(MODEL2, ResourceType.FILE).addTag(ResourceTag.NECESSARY);

		createResultDescr(ADMISSIBLE, ResourceType.BOOL).addTag(ResourceTag.NECESSARY);
	}

	boolean parseInput()
	{
		ResourceFile resModel1 = getResourceWithType(MODEL1, false);
		ResourceFile resModel2 = getResourceWithType(MODEL2, false);

		if (resModel1 != null)
			fileModel1 = resModel1.getData();
		if (resModel2 != null)
			fileModel2 = resModel2.getData();
		return true;
	}

	@Override
	public JobState task()
	{
		parseInput();
		if ((fileModel1 == null) || (fileModel2 == null))
			return endError("Missing Input File");

		AdmissibilityCheck check = new AdmissibilityCheck(this);
		result = check.checkEquivalence(fileModel1, fileModel2);
		return end(JobResult.OK);
	}

	/*
	 * private String getFolder() { if (folder == null) { ResourceInterface res
	 * = descrFolder.getResource(); if ((res != null) && (res.getType() ==
	 * descrFolder.getType())) folder = (ResourceFolder) res; } if (folder ==
	 * null) return "."; return folder.getData(); }
	 */

	@Override
	public ResourceInterface getResultResource(String name)
	{
		if (ADMISSIBLE.equals(name))
		{
			ResourceBool bool = new ResourceBool();
			if (result == null)
				return null;
			bool.setDataValue(result.isAdmisible());
			return bool;
		}
		return super.getResultResource(name);
	}
}
