package kn.uni.sen.joblibrary.tartar.web;

import org.springframework.boot.SpringApplication;
import org.springframework.boot.autoconfigure.SpringBootApplication;

import kn.uni.sen.joblibrary.tartar.experiment.LibraryTarTar_Console;
import kn.uni.sen.joblibrary.tartar.gui.MainGui;

@SpringBootApplication
public class TarTarMain extends TarTarWeb
{
	public static void main(String[] args)
	{
		if (args.length == 0)
			MainGui.main(args);
		else if ("-web".equals(args[0].toLowerCase().replace("--", "-")))
			SpringApplication.run(TarTarMain.class, args);
		else
		{
			LibraryTarTar_Console.main(args);
		}
	}
}
