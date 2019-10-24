package kn.uni.sen.joblibrary.tartar.job_admissibility;

import kn.uni.sen.joblibrary.tartar.admissibility.AdmissibilityCheck;
import kn.uni.sen.joblibrary.tartar.common.ResultAdm;
import kn.uni.sen.joblibrary.tartar.common.TarTarConfiguration;
import kn.uni.sen.jobscheduler.common.impl.JobAbstract;
import kn.uni.sen.jobscheduler.common.model.EventHandler;
import kn.uni.sen.jobscheduler.common.model.JobResult;
import kn.uni.sen.jobscheduler.common.model.JobState;
import kn.uni.sen.jobscheduler.common.resource.ResourceBool;
import kn.uni.sen.jobscheduler.common.resource.ResourceDescription;
import kn.uni.sen.jobscheduler.common.resource.ResourceFile;
import kn.uni.sen.jobscheduler.common.resource.ResourceInterface;
import kn.uni.sen.jobscheduler.common.resource.ResourceTag;
import kn.uni.sen.jobscheduler.common.resource.ResourceType;

public class Job_Admissibility extends JobAbstract
{
	protected ResourceDescription descrModel1 = new ResourceDescription("Model1", ResourceType.FILE);
	protected ResourceDescription descrModel2 = new ResourceDescription("Model2", ResourceType.FILE);

	protected ResourceDescription descrResultAdm = new ResourceDescription("Admissible", ResourceType.BOOL);

	String fileModel1 = null;
	String fileModel2 = null;
	ResultAdm result = null;

	public Job_Admissibility()
	{
		this(null);
	}

	public Job_Admissibility(EventHandler father)
	{
		super(father);
		this.version = TarTarConfiguration.getVersion();

		this.addInputDescription(descrModel1);
		descrModel1.addTag(ResourceTag.NECESSARY);
		this.addInputDescription(descrModel2);
		descrModel2.addTag(ResourceTag.NECESSARY);

		this.addResultDescription(descrResultAdm);
	}

	boolean parseInput()
	{
		ResourceFile resModel1 = descrModel1.getResourceWithType();
		ResourceFile resModel2 = descrModel2.getResourceWithType();

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

		AdmissibilityCheck check = new AdmissibilityCheck(jobContext);
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
	public ResourceInterface getResource(String name, boolean out)
	{
		if (name.equals(descrResultAdm.getName()))
		{
			ResourceBool bool = new ResourceBool();
			if (result == null)
				return null;
			bool.setDataValue(result.isAdmisible());
			return bool;
		}
		return null;
	}
}
