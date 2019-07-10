package kn.uni.sen.tartar.gui;

import java.awt.GridLayout;
import java.io.File;
import java.io.FilenameFilter;
import javax.swing.JPanel;
import javax.swing.JTextField;

import kn.uni.sen.tartar.MainDiagnostic;

public class GuiVersion extends GuiAbstract
{
	GuiVersion()
	{
		super(null);
	}

	@Override
	JPanel createGui()
	{
		JTextField field = new JTextField("Version: " + MainDiagnostic.version);
		JPanel panel = new JPanel();
		panel.setLayout(new GridLayout(1, 1));
		panel.add(field);
		return panel;
	}

	boolean startAction()
	{
		return false;
	}

	@Override
	void checkStatus()
	{
		reset();
	}

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

	public void reset()
	{
		resetSystemStreams();
	}

	@Override
	RunParameter getProgram()
	{
		return null;
	}
}
