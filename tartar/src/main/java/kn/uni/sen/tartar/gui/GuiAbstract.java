package kn.uni.sen.tartar.gui;

import java.awt.TextArea;
import java.awt.event.ActionListener;
import java.io.IOException;
import java.io.OutputStream;
import java.io.PrintStream;

import javax.swing.JPanel;
import javax.swing.SwingUtilities;

public abstract class GuiAbstract
{
	String OriginalPath;

	PrintStream StdOut;
	PrintStream StdErr;

	ActionListener Listener;

	GuiAbstract(ActionListener listener)
	{
		Listener = listener;
	}

	public void setOriginalPath(String path)
	{
		OriginalPath = path;
	}

	abstract JPanel createGui();

	abstract boolean startAction();
	
	abstract RunParameter getProgram();

	// Followings are The Methods that do the Redirect, you can simply Ignore
	// them.
	protected void redirectSystemStreams(TextArea textArea)
	{
		StdOut = System.out;
		StdErr = System.err;
		if (textArea == null)
			return;
		OutputStream out = new OutputStream()
		{
			@Override
			public void write(int b) throws IOException
			{
				updateTextArea(textArea, String.valueOf((char) b));
			}

			@Override
			public void write(byte[] b, int off, int len) throws IOException
			{
				updateTextArea(textArea, new String(b, off, len));
			}

			@Override
			public void write(byte[] b) throws IOException
			{
				write(b, 0, b.length);
			}
		};

		System.setOut(new PrintStream(out, true));
		// System.setErr(new PrintStream(out, true));
	}

	private void updateTextArea(TextArea textArea, final String text)
	{
		SwingUtilities.invokeLater(new Runnable()
		{
			public void run()
			{
				textArea.append(text);
			}
		});
	}

	protected void resetSystemStreams()
	{
		if (StdOut != null)
			System.setOut(StdOut);
		StdOut = null;
		if (StdErr != null)
			System.setErr(StdErr);
		StdErr = null;
	}

	abstract void checkStatus();

	abstract void reset();
}
