package kn.uni.sen.joblibrary.tartar.convert;

import org.sosy_lab.common.ShutdownManager;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.BasicLogManager;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.SolverContext;

public class SMTContext
{
	public static SolverContext createContext(Solvers solverOption)
	{
		Configuration config;
		try
		{
			config = Configuration.defaultConfiguration();// fromCmdLineArguments(args);
			LogManager logger = BasicLogManager.create(config);
			ShutdownManager shutdown = ShutdownManager.create();

			// SolverContext is a class wrapping a solver context.
			// Solver can be selected either using an argument or a
			// configuration
			// option inside `config`.
			return SolverContextFactory.createSolverContext(config, logger, shutdown.getNotifier(), solverOption);
		} catch (InvalidConfigurationException e)
		{
			e.printStackTrace();
		}
		return null;
	}
}
