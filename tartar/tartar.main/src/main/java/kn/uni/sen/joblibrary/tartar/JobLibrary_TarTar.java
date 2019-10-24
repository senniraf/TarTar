package kn.uni.sen.joblibrary.tartar;

import java.lang.reflect.Constructor;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import kn.uni.sen.joblibrary.tartar.job_admissibility.Job_Admissibility;
import kn.uni.sen.joblibrary.tartar.job_repaircomputation.Job_RepairComputation;
import kn.uni.sen.joblibrary.tartar.job_uppaal2smt2.Job_Uppaal2Smt2;
import kn.uni.sen.joblibrary_tartar.job_experiment.Job_SeedExperiment;
import kn.uni.sen.jobscheduler.common.impl.JobLibraryAbstract;
import kn.uni.sen.jobscheduler.common.model.EventHandler;
import kn.uni.sen.jobscheduler.common.model.Job;

public class JobLibrary_TarTar extends JobLibraryAbstract
{
	List<Class<? extends Job>> JobList;

	public JobLibrary_TarTar()
	{
		this(JobLibrary_TarTar.class.getSimpleName());
	}

	public JobLibrary_TarTar(String libraryName)
	{
		JobList = new LinkedList<Class<? extends Job>>();

		if (libraryName == null)
			return;

		if (getLibraryName().compareTo(libraryName) == 0)
		{
			JobList.add(Job_Uppaal2Smt2.class);
			JobList.add(Job_RepairComputation.class);
			JobList.add(Job_Admissibility.class);
			JobList.add(Job_SeedExperiment.class);
		}
	}

	@Override
	public String getLibaryVersion()
	{
		return "JV_3.0";
	}

	@Override
	public String getLibraryName()
	{
		return this.getClass().getSimpleName();
	}

	@Override
	public List<Class<? extends Job>> getJobList()
	{
		return JobList;
	}

	@Override
	public Job createJob(String jobName, String version, EventHandler father)
	{
		for (Iterator<Class<? extends Job>> it = JobList.iterator(); it.hasNext();)
		{
			Class<? extends Job> jobClass = it.next();
			try
			{
				Job job = null;
				Constructor<? extends Job> con = jobClass.getDeclaredConstructor(EventHandler.class);
				if (con != null)
					job = con.newInstance(father);
				else
				{
					con = jobClass.getDeclaredConstructor(EventHandler.class);
					if (con != null)
						job = con.newInstance();
				}

				if (job.getJobName().compareTo(jobName) == 0)
				{
					if ((version == null) || (version.compareTo("") == 0))
						return job;
					if (job.getJobVersion().compareTo(version) == 0)
						return job;
				}
			} catch (Exception ex)
			{
			}
		}
		return null;
	}
}
