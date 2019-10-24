package kn.uni.sen.joblibrary.tartar.web.form;

import java.io.File;
import java.net.URL;
import java.util.LinkedList;
import java.util.List;

import org.springframework.web.multipart.MultipartFile;

import kn.uni.sen.jobscheduler.common.resource.ResourceFile;

public class UploadForm
{
	private String description = "";
	private String fileName = "";

	// Upload files.
	private String exampleFile = "";
	private MultipartFile[] fileDatas = new MultipartFile[] {};
	private List<String> fileNames = new LinkedList<>();
	// private File model;

	public UploadForm()
	{
		// System.out.print("here");
	}

	public String getDescription()
	{
		return description;
	}

	public void setDescription(String description)
	{
		this.description = description;
	}

	public String getFileName()
	{
		return fileName;
	}

	public void setFileName(String fileName)
	{
		this.fileName = fileName;
	}

	public MultipartFile[] getFileDatas()
	{
		return fileDatas;
	}

	public void setFileDatas(MultipartFile[] fileDatas)
	{
		this.fileDatas = fileDatas;
		if (fileDatas.length >= 1)
			setFileName(fileDatas[0].getOriginalFilename());
		System.out.println(getFileName());
	}

	public void setFileNameList(List<String> fileNameList)
	{
		this.fileNames = fileNameList;
	}

	public List<String> getFileNames()
	{
		return fileNames;
	}

	public String getExampleFile()
	{
		return exampleFile;
	}

	public void setExampleFile(String file)
	{
		exampleFile = file;
	}

	public File getModel(String fileName)
	{
		if (fileName == null)
			return null;
		// found the model in the modelList
		fileName += ".xml";
		ClassLoader classLoader = getClass().getClassLoader();
		URL fileURL = classLoader.getResource(fileName);

		// String filePath = fileURL.getPath();
		String file = ResourceFile.writeURL2File(fileURL, "result");
		if (file == null)
		{
			return null;
		}
		File model = new File(file);
		return model;
	}

}
