package kn.uni.sen.tartar.admissible;

public class FileChange
{
	// name of file which was corrupted
	String file;
	// changed text in file
	Repair corruption;

	public FileChange(String file, Repair corruption)
	{
		this.file = file;
		this.corruption = corruption;
	}

	public String getFile()
	{
		return file;
	}

	public String getText()
	{
		if (corruption == null)
			return "";
		return corruption.getModificationText();
	}
}
