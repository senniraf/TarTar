package kn.uni.sen.tartar.gui;

import java.awt.Dimension;
import java.awt.GridLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.File;
import java.io.FilenameFilter;
import java.util.LinkedList;
import java.util.List;

import javax.swing.ButtonGroup;
import javax.swing.JButton;
import javax.swing.JComboBox;
import javax.swing.JFileChooser;
import javax.swing.JFrame;
import javax.swing.JPanel;
import javax.swing.JRadioButton;
import javax.swing.JTextField;
import javax.swing.filechooser.FileNameExtensionFilter;
import javax.swing.filechooser.FileSystemView;

import kn.uni.sen.tartar.UppaalApi;
import kn.uni.sen.tartar.uppaal2smt2.SMT2_OPTION;
import kn.uni.sen.tartar.util.Helper;

public class GuiParameter extends GuiAbstract
{
	RunParameter diagnostic;

	SMT2_OPTION[] modifyList = { SMT2_OPTION.BOUNDARY, SMT2_OPTION.RESET, SMT2_OPTION.REFERENCE, SMT2_OPTION.URGENT,
			SMT2_OPTION.COMPARISON };

	SMT2_OPTION[] outputList = { SMT2_OPTION.ELIMINATION }; // ,
															// SMT2_OPTION.FUNCTION
															// };

	JTextField TraceFileText;
	JTextField ModelFileText;

	List<JRadioButton> modifyButtonList = new LinkedList<>();
	List<JRadioButton> outputButtonList = new LinkedList<>();

	boolean BExperiment = false;

	GuiParameter(ActionListener listener, boolean experiment)
	{
		super(listener);
		BExperiment = experiment;
	}

	@Override
	JPanel createGui()
	{
		JPanel panel = new JPanel();
		// panel.setPreferredSize(new Dimension(400, 300));
		int gridRows = BExperiment ? 3 : 4;
		panel.setLayout(new GridLayout(gridRows, 1));

		JPanel panelModelFile = new JPanel();
		panelModelFile.setLayout(new GridLayout(1, 2));
		String extra = BExperiment ? "good" : "bad";
		ModelFileText = new JTextField("Select Uppaal " + extra + " Model File");
		JButton modelFileButton = new JButton("Search File");
		modelFileButton.addActionListener(new SearchFile("Select a Uppaal Model file", "xml", ModelFileText));
		panelModelFile.add(ModelFileText);
		panelModelFile.add(modelFileButton);

		JPanel panelTraceFile = new JPanel();
		panelTraceFile.setLayout(new GridLayout(1, 2));
		TraceFileText = new JTextField("Select Uppaal Trace File (Optional)");
		JButton traceFileButton = new JButton("Search File");
		traceFileButton.addActionListener(new SearchFile("Select a Uppaal Trace file", "xml", TraceFileText));
		panelTraceFile.add(TraceFileText);
		panelTraceFile.add(traceFileButton);

		JButton startButton = new JButton("Start");
		startButton.setPreferredSize(new Dimension(400, 30));
		startButton.addActionListener(Listener);

		JComboBox<String> analysisComboBox = new JComboBox<>();
		// ModeComboBox.addItem("Select algorithm");
		analysisComboBox.setPreferredSize(new Dimension(400, 30));
		analysisComboBox.addItem("QE");
		analysisComboBox.addItem("Function");

		JPanel optionsCheckBoxes = new JPanel();
		optionsCheckBoxes.setLayout(new GridLayout(1, 2));

		ButtonGroup modifyGroup = new ButtonGroup();
		JPanel modifyPanel = new JPanel();
		modifyPanel.setLayout(new GridLayout(modifyList.length, 1));
		boolean first = true;
		for (SMT2_OPTION opt : modifyList)
		{
			JRadioButton but = new JRadioButton(SMT2_OPTION.getLongName(opt));
			// birdButton.setMnemonic(KeyEvent.VK_B);
			but.setActionCommand(SMT2_OPTION.getName(opt));
			modifyGroup.add(but);
			modifyPanel.add(but);
			modifyButtonList.add(but);
			if (first)
			{
				first = false;
				but.setSelected(true);
			}
		}

		ButtonGroup outputGroup = new ButtonGroup();
		JPanel outputPanel = new JPanel();
		outputPanel.setLayout(new GridLayout(outputList.length, 1));
		first = true;
		for (SMT2_OPTION opt : outputList)
		{
			JRadioButton but = new JRadioButton(SMT2_OPTION.getLongName(opt));
			// birdButton.setMnemonic(KeyEvent.VK_B);
			but.setActionCommand(SMT2_OPTION.getName(opt));
			outputGroup.add(but);
			outputPanel.add(but);
			outputButtonList.add(but);
			if (first)
			{
				first = false;
				but.setSelected(true);
			}
		}

		optionsCheckBoxes.add(modifyPanel);
		optionsCheckBoxes.add(outputPanel);

		// new panel for placing the buttons to the screen
		panel.add(panelModelFile);
		if (!!!BExperiment)
			panel.add(panelTraceFile);
		panel.add(optionsCheckBoxes);
		panel.add(startButton);
		panel.setOpaque(true);
		return panel;
	}

	boolean startAction()
	{
		diagnostic = new RunParameter();

		diagnostic.setExperiment(BExperiment);
		String modelPath = ModelFileText.getText();
		if (!!!Helper.checkExists(modelPath))
			return false;
		diagnostic.setModelFile(modelPath);

		String tracePath = TraceFileText.getText();
		if (!!!Helper.checkExists(tracePath))
		{
			if (!!!UppaalApi.checkVersion())
				return false;
		} else
			diagnostic.setTraceFile(tracePath);
		for (JRadioButton but : modifyButtonList)
		{
			if (but.isSelected())
				diagnostic.setOption(SMT2_OPTION.getOption(but.getActionCommand()));
		}
		for (JRadioButton but : outputButtonList)
		{
			if (but.isSelected())
				diagnostic.setOption(SMT2_OPTION.getOption(but.getActionCommand()));
		}
		return true;
	}

	@Override
	void checkStatus()
	{
		if (diagnostic == null)
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

	public File findImage(String dirName)
	{
		File[] files = fileFinder(dirName, ".png");
		if (files.length > 0)
			return files[0];
		return null;
	}

	class SearchFile implements ActionListener
	{
		String filePath;
		String headline;
		String type;
		JTextField textField;

		SearchFile(String headline, String type, JTextField textField)
		{
			this.headline = headline;
			this.type = type;
			this.textField = textField;
		}

		String getFilePath()
		{
			return filePath;
		}

		@Override
		public void actionPerformed(ActionEvent e)
		{
			JFileChooser XMIfileChooser = new JFileChooser(FileSystemView.getFileSystemView().getHomeDirectory());
			FileNameExtensionFilter filter = new FileNameExtensionFilter(type.toUpperCase(), type);
			XMIfileChooser.setFileFilter(filter);

			JPanel XMIfileChooserPanel = new JPanel();
			XMIfileChooserPanel.add(XMIfileChooser);
			XMIfileChooserPanel.setVisible(true);

			JFrame frame1 = new JFrame(headline);

			frame1.add(XMIfileChooserPanel);
			frame1.pack();
			frame1.revalidate();
			frame1.setLocationRelativeTo(null);
			frame1.setVisible(true);
			int returnValue = XMIfileChooser.showOpenDialog(null);
			frame1.setVisible(false);

			if (returnValue != JFileChooser.APPROVE_OPTION)
				return;

			File selectedXmiFile = XMIfileChooser.getSelectedFile();
			if (textField != null)
				textField.setText(selectedXmiFile.getPath());
		}
	}

	public void reset()
	{
		resetSystemStreams();
	}

	@Override
	RunParameter getProgram()
	{
		return diagnostic;
	}
}
