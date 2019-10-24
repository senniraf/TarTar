package kn.uni.sen.joblibrary.tartar.gui;

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

import kn.uni.sen.joblibrary.tartar.common.SMT2_OPTION;
import kn.uni.sen.joblibrary.tartar.job_repaircomputation.Job_RepairComputation;
import kn.uni.sen.joblibrary.tartar.job_repaircomputation.ProgramEvent;
import kn.uni.sen.joblibrary.tartar.job_repaircomputation.ProgramStatus;
import kn.uni.sen.joblibrary_tartar.job_experiment.Job_SeedExperiment;
import kn.uni.sen.jobscheduler.common.impl.JobContextSimple;
import kn.uni.sen.jobscheduler.common.impl.JobDataInput;
import kn.uni.sen.jobscheduler.common.impl.LogConsole;
import kn.uni.sen.jobscheduler.common.model.Job;
import kn.uni.sen.jobscheduler.common.resource.Helper;
import kn.uni.sen.jobscheduler.common.resource.ResourceEnum;
import kn.uni.sen.jobscheduler.common.resource.ResourceFile;
import kn.uni.sen.jobscheduler.common.resource.ResourceList;

public class GuiResult extends GuiAbstract implements ProgramEvent
{
	RunParameter Parameter;
	TextArea Output;
	JTextArea Result;
	Job job;
	JobDataInput inputData = new JobDataInput();
	JobContextSimple context = JobContextSimple.createDummy("Gui");
	{
		context.handler().subscribe(new LogConsole());
	}

	public GuiResult(RunParameter para)
	{
		super(null);
		this.Parameter = para;

		if (Parameter.isExperiment())
			job = new Job_SeedExperiment(context.handler());
		else
			job = new Job_RepairComputation(context.handler());

		JobDataInput inData = new JobDataInput();
		job.addLogger(new LogConsole(1));
		inData.add("Model", new ResourceFile(para.getModelFile()));
		inData.add("Trace", new ResourceFile(para.getTraceFile()));
		ResourceList list = new ResourceList();
		for (SMT2_OPTION opt : para.getOptionList())
			list.addResource(new ResourceEnum(opt));
		inData.add("ParameterList", list);
		inData.add("RepairKind", new ResourceEnum(para.getRepair()));
		inData.add("SeedKind", new ResourceEnum(para.getRepair()));

		Helper.setResourceSource(job.getInputDescription(), inData);
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
				String folder = System.getProperty("user.dir") + "/result";
				try
				{
					// opensuse
					Runtime.getRuntime().exec("dolphin " + folder);
					// Desktop.getDesktop().open(new File(folder + "/test"));
					return;
				} catch (IOException e1)
				{
					// e1.printStackTrace();
				}
				try
				{
					// windows
					Runtime.getRuntime().exec("explorer " + folder);
					return;
				} catch (IOException e1)
				{
					// e1.printStackTrace();
				}
				try
				{
					// ubuntu
					Runtime.getRuntime().exec("nautilus " + folder);
					return;
				} catch (IOException e1)
				{
					// e1.printStackTrace();
				}
			}
		});
		Output = new TextArea();
		Result = new JTextArea();
		Border border = BorderFactory.createLineBorder(Color.BLACK);
		Result.setBorder(BorderFactory.createCompoundBorder(border, BorderFactory.createEmptyBorder(10, 10, 10, 10)));

		redirectSystemStreams(Output);

		JPanel panel = new JPanel();
		panel.setLayout(new GridLayout(2, 1));
		panel.add(folderButton);
		panel.add(Output);
		//panel.add(Result);
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
