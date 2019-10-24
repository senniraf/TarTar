package kn.uni.sen.joblibrary.tartar.web.model;

import java.io.BufferedOutputStream;
import java.io.File;
import java.io.FileOutputStream;
import java.io.FilenameFilter;
import java.util.ArrayList;
import java.util.List;

import javax.servlet.http.HttpServletRequest;

import org.springframework.web.multipart.MultipartFile;

import kn.uni.sen.joblibrary.tartar.common.SMT2_OPTION;
import kn.uni.sen.joblibrary.tartar.gui.AnalysisTarTarType;
import kn.uni.sen.joblibrary.tartar.modifymodel.ParsePropertyModel;
import kn.uni.sen.joblibrary.tartar.modifymodel.ParsePropertyModel.Property;
import kn.uni.sen.joblibrary.tartar.web.form.OptionsForm;
import kn.uni.sen.joblibrary.tartar.web.form.UploadForm;
import kn.uni.sen.jobscheduler.common.impl.JobContextSimple;
import kn.uni.sen.jobscheduler.common.model.JobContext;
import kn.uni.sen.jobscheduler.common.model.JobEvent;
import kn.uni.sen.jobscheduler.common.resource.ResourceEnum;
import kn.uni.sen.jobscheduler.common.resource.ResourceFile;
import kn.uni.sen.jobscheduler.common.resource.ResourceFolder;
import kn.uni.sen.jobscheduler.common.resource.ResourceInteger;
import kn.uni.sen.jobscheduler.common.resource.ResourceString;

public class JobWebSessionTarTar extends JobWebSessionAbstract
{
	BufferLogger logger = new BufferLogger(1000);
	JobContext context = new JobContextSimple(null, "WebGui", new ResourceFolder("result"));
	private String filePath;
	private long tStart = 0;
	AnalysisTarTarType analysisType = AnalysisTarTarType.ANALYSIS_UNKOWN;

	TarTarClient jobClient;

	public JobWebSessionTarTar(Integer id)
	{
		super(id);
		context.handler().subscribe(logger);
	}

	public void setStartTime()
	{
		this.tStart = System.currentTimeMillis();
	}

	public long getStartTime()
	{
		return tStart;
	}

	/**
	 * create a JobClient_QuantUM if not yet existing
	 */
	void createClient()
	{
		if (jobClient != null)
			return;
		jobClient = new TarTarClient(context);
	}

	/**
	 * Uses an xml file and does the model transformation
	 * 
	 * @param modelFile
	 *            xml file
	 */
	public boolean parseModel()
	{
		if (filePath == null)
			return false;
		createClient();
		// clientQuantUM.loadXMIModel(filePath,
		// AnalysisQuantUMType.ANALYSIS_CAUSE);
		return true;
	}

	List<Property> propList = null;

	public String[] getPropertyList()
	{
		propList = new ParsePropertyModel(filePath).getPropList();
		if (propList == null)
			return new String[] {};
		List<String> list = new ArrayList<>();
		for (Property p : propList)
		{
			String form = p.form;
			if (!!!form.isEmpty())
				list.add(form);
		}
		return list.toArray(new String[] {});
	}

	int getIndexProperty(String prop)
	{
		if ((propList == null) || (prop == null))
			return 0;
		for (Property p : propList)
		{
			prop.equals(p.form);
			return p.index;
		}
		return 0;
	}

	/**
	 * starts the model verification
	 */
	public void verifyModel()
	{
		if (jobClient == null)
			return;
		Thread thread = new Thread(jobClient);
		thread.start();
	}

	/**
	 * ugly hack to get png image file from a folder
	 * 
	 * @param dirName
	 * @return image file if existing
	 */
	public File findImage(String dirName)
	{
		File[] files = fileFinder(dirName, ".png");
		if (files.length > 0)
			return files[0];
		return null;
	}

	/**
	 * searches inside a folder for files with a certain extension
	 * 
	 * @param dirName
	 * @param ext
	 * @return array of files
	 */
	public File[] fileFinder(String dirName, String ext)
	{
		File dir = new File(dirName);

		return dir.listFiles(new FilenameFilter()
		{
			public boolean accept(File dir, String filename)
			{
				return filename.endsWith(ext);
			}
		});
	}

	public boolean doUpload(HttpServletRequest request, UploadForm UploadFormObject, JobWebSessionTarTar session)
	{
		String fileName = UploadFormObject.getFileName();
		String exampleFile = UploadFormObject.getExampleFile();
		if ((exampleFile != null) && exampleFile.length() > 0 && fileName.equals(""))
		// use example file
		{
			try
			{
				// add the file to the session
				File file = UploadFormObject.getModel(exampleFile);
				String filePath = file.getAbsolutePath();
				context.logEventStatus(JobEvent.DEBUG, "filePath " + filePath);
				session.setFile(filePath);
			} catch (Exception e)
			{
				context.logEventStatus(JobEvent.ERROR, "File upload error!");
				return false;
			}
			return true;
		}

		// user upload file
		// Root Directory.
		String uploadRootPath = request.getServletContext().getRealPath("upload");
		System.out.println("uploadRootPath=" + uploadRootPath);

		File uploadRootDir = new File(uploadRootPath);
		// Create directory if it not exists.
		if (!uploadRootDir.exists())
			uploadRootDir.mkdirs();

		MultipartFile[] fileDatas = UploadFormObject.getFileDatas();
		int count = 0;
		for (MultipartFile fileData : fileDatas)
		{
			// Client File Name
			fileName = fileData.getOriginalFilename();
			System.out.println("Client File Name = " + fileName);
			if (fileName != null && fileName.length() > 0)
			{
				try
				{
					// Create the file at server
					String filePath = uploadRootDir.getAbsolutePath() + File.separator + fileName;
					File serverFile = new File(filePath);
					setFile(filePath);
					BufferedOutputStream stream = new BufferedOutputStream(new FileOutputStream(serverFile));
					stream.write(fileData.getBytes());
					stream.close();
					count++;
				} catch (Exception e)
				{
					context.logEventStatus(JobEvent.ERROR, "File upload error!");
					return false;
				}
			}
		}
		return count != 0;
	}

	public void setFile(String file)
	{
		filePath = file;
	}

	public boolean hasStarted()
	{
		return false;
	}

	public void setAnalysisType(AnalysisTarTarType type)
	{
		analysisType = type;
	}

	public AnalysisTarTarType getAnalysisType()
	{
		return analysisType;
	}

	public JobEvent getNextEvent()
	{
		if (jobClient == null)
			return null;
		return logger.getNextEvent();
	}

	public String[] getOptionList()
	{
		List<String> list = new ArrayList<>();
		for (SMT2_OPTION opt : SMT2_OPTION.ListModifier)
			list.add(SMT2_OPTION.getLongName(opt));
		return list.toArray(new String[] {});
	}

	public void setOptions(OptionsForm form)
	{
		if (jobClient == null)
			return;
		jobClient.setAnalysis(analysisType);
		ResourceFile resModel = new ResourceFile(filePath);
		jobClient.add("Model", resModel);
		int time = form.getTimeZ3();
		if (time > 0)
			jobClient.add("Timeout", new ResourceInteger(time));

		ResourceEnum opt = new ResourceEnum(SMT2_OPTION.getOption(form.getOptionName()));
		//ResourceList paraList = new ResourceList();
		//paraList.addResource(opt);
		//jobClient.add("ParameterList", paraList);
		jobClient.add("RepairKind", opt);
		jobClient.add("SeedKind", opt);

		int propIndex = getIndexProperty(form.getPropertyName());
		if (propIndex >= 1)
		{
			ResourceString prop = new ResourceString("" + propIndex);
			jobClient.add("Property", prop);
		}
	}
}
