package kn.uni.sen.tartar.gui;

import java.awt.Color;
import java.awt.GridLayout;
import java.awt.TextArea;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.File;
import java.io.FilenameFilter;
import java.io.IOException;

import javax.swing.BorderFactory;
import javax.swing.JButton;
import javax.swing.JPanel;
import javax.swing.JTextArea;
import javax.swing.border.Border;

import kn.uni.sen.tartar.Experiment;
import kn.uni.sen.tartar.Job2;
import kn.uni.sen.tartar.MainDiagnostic;
import kn.uni.sen.tartar.ProgramEvent;
import kn.uni.sen.tartar.ProgramStatus;
import kn.uni.sen.tartar.uppaal2smt2.SMT2_OPTION;

public class GuiResult extends GuiAbstract implements ProgramEvent
{
	RunParameter Parameter;
	TextArea Output;
	JTextArea Result;
	Job2 job;

	public GuiResult(RunParameter para)
	{
		super(null);
		this.Parameter = para;

		if (Parameter.isExperiment())
			job = new Experiment();
		else
			job = new MainDiagnostic();
		job.setModelFile(para.getModelFile());
		job.setTraceFile(para.getTraceFile());
		for (SMT2_OPTION opt : para.getOptionList())
			job.setOption(opt);
		job.setProgramEvent(this);

	}

	public class DiagnosticThread extends Thread
	{
		public void run()
		{
			job.start();
		}
	}

	@Override
	JPanel createGui()
	{
		JButton folderButton = new JButton("Open Result Folder");
		folderButton.addActionListener(new ActionListener()
		{
			@Override
			public void actionPerformed(ActionEvent arg0)
			{
				String folder = System.getProperty("user.dir") + "/test";
				try
				{
					Runtime.getRuntime().exec("dolphin " + folder);
					// Desktop.getDesktop().open(new File(folder + "/test"));
					return;
				} catch (IOException e1)
				{
					e1.printStackTrace();
				}
				try
				{
					Runtime.getRuntime().exec("explorer " + folder);
					return;
				} catch (IOException e1)
				{
					e1.printStackTrace();
				}
			}
		});
		Output = new TextArea();
		Result = new JTextArea();
		Border border = BorderFactory.createLineBorder(Color.BLACK);
		Result.setBorder(BorderFactory.createCompoundBorder(border, BorderFactory.createEmptyBorder(10, 10, 10, 10)));

		redirectSystemStreams(Output);

		JPanel panel = new JPanel();
		panel.setLayout(new GridLayout(3, 1));
		panel.add(folderButton);
		panel.add(Output);
		panel.add(Result);
		panel.setOpaque(true);

		Thread thread = new DiagnosticThread();
		thread.start();

		return panel;
	}

	boolean startAction()
	{
		return false;
	}

	@Override
	void checkStatus()
	{
		if (job == null)
			return;
		// if (!!!diagnostic.getState())
		// return;
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
		return null; // diagnostic;
	}

	@Override
	public synchronized void changeStatus(ProgramStatus status)
	{
		if (status == ProgramStatus.RUN)
			Output.setText(Output.getText() + "\n Diagnose Start");
		if (status == ProgramStatus.STOP)
		{
			Output.setText(Output.getText() + "\n Diagnose End");
		}
	}

	@Override
	public synchronized void changeValue(String result)
	{
		Result.setText(Result.getText() + "\n" + result);
	}
}
