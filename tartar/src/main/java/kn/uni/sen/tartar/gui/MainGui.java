package kn.uni.sen.tartar.gui;

import java.awt.BorderLayout;
import java.awt.Dimension;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.JButton;
import javax.swing.JFrame;
import javax.swing.JMenuBar;
import javax.swing.JPanel;
import javax.swing.SwingConstants;
import javax.swing.UIManager;
import javax.swing.UIManager.LookAndFeelInfo;

/**
 * This is the Gui. No work is done here and no data are stored.
 * 
 * @author Martin Koelbl
 */
public class MainGui
{
	private JFrame frame;
	private JMenuBar MenuBar;
	private JButton NewMenu;
	private JButton ExpMenu;
	private JButton VersionMenu;

	String originalPath;

	GuiAbstract Gui;
	JPanel GuiPanel;

	public static void main(String[] args)
	{
		MainGui quantumGui = new MainGui();
		quantumGui.createGUI();
	}

	void createGUI()
	{
		frame = new JFrame("Uppaal2Smt2");
		frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
		frame.setPreferredSize(new Dimension(400, 300));

		frame.add(initialMenuContent(false), BorderLayout.CENTER);

		MenuBar = new JMenuBar();
		// build the File menu
		NewMenu = new JButton("New Analysis");
		NewMenu.addActionListener(new MenuActionListener());
		NewMenu.setActionCommand("Analysis");
		// NewMenu.addMouseListener(new MenuListener("New"));

		ExpMenu = new JButton("New Experiment");
		ExpMenu.addActionListener(new MenuActionListener());
		ExpMenu.setActionCommand("Experiment");

		// build the Help menu
		VersionMenu = new JButton("Version");
		VersionMenu.setActionCommand("Version");
		VersionMenu.addActionListener(new MenuActionListener());
		// VersionMenu.addActionListener(new MenuActionListener());
		// LastModelsMenu.addMouseListener(new MenuListener("Version"));

		// add menus to menubar
		MenuBar.add(NewMenu);
		MenuBar.add(ExpMenu);
		MenuBar.add(VersionMenu);

		// Display the window
		frame.setJMenuBar(MenuBar);
		frame.pack();
		frame.setLocationRelativeTo(null);
		frame.setVisible(true);
	}

	// this function creates the menu containing new xmi selection, last models
	// and last results.
	public JPanel initialMenuContent(boolean exp)
	{
		Gui = new GuiParameter(new GuiStart(), exp);
		GuiPanel = Gui.createGui();
		return GuiPanel;
	}

	public JPanel versionMenuContent()
	{
		Gui = new GuiVersion();
		GuiPanel = Gui.createGui();
		return GuiPanel;
	}

	class MenuActionListener implements ActionListener
	{
		public void actionPerformed(ActionEvent e)
		{
			reset();
			frame.getContentPane().removeAll();
			frame.pack();
			frame.validate();

			if (e.getActionCommand().compareTo("Version") == 0)
			{
				frame.add(versionMenuContent(), BorderLayout.CENTER);
			} else if (e.getActionCommand().compareTo("Experiment") == 0)
			{
				frame.add(initialMenuContent(true), BorderLayout.CENTER);
			} else
			{
				frame.add(initialMenuContent(false), BorderLayout.CENTER);
			}
			frame.pack();
			frame.validate();
		}
	}

	void useNiceElements()
	{
		try
		{
			for (LookAndFeelInfo info : UIManager.getInstalledLookAndFeels())
			{
				if ("Nimbus".equals(info.getName()))
				{
					UIManager.setLookAndFeel(info.getClassName());
					break;
				}
			}
		} catch (Exception e)
		{
			// If Nimbus is not available, you can set the GUI to another look
			// and feel.
			// JobEvent event = logger.logEvent("SwingError", "Swing Look and
			// Feel Nimbus not available.");
			// event.addTag("warning");
		}
	}

	class GuiStart implements ActionListener
	{
		@Override
		public void actionPerformed(ActionEvent e)
		{
			if ((Gui == null) || !!!Gui.startAction())
				return;

			if (GuiPanel != null)
			{
				frame.getContentPane().remove(GuiPanel);
				GuiPanel = null;
				frame.getContentPane().revalidate();
				frame.getContentPane().repaint();
			}

			Gui = new GuiResult(Gui.getProgram());
			GuiPanel = Gui.createGui();
			frame.getContentPane().add(GuiPanel, SwingConstants.CENTER);
			frame.pack();
			frame.getContentPane().revalidate();
			frame.getContentPane().repaint();
			// frame.setPreferredSize(new Dimension(600, 600));
		}
	};

	private void reset()
	{
		if (Gui != null)
			Gui.reset();
		Gui = null;
	}
}
