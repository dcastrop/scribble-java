/**
 * Copyright 2008 The Scribble Authors
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 * in compliance with the License. You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software distributed under the License
 * is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
 * or implied. See the License for the specific language governing permissions and limitations under
 * the License.
 */
package org.scribble.cli;

import java.io.File;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Consumer;
import java.util.stream.Collectors;

import org.scribble.ast.Module;
import org.scribble.ast.ProtocolDecl;
import org.scribble.ast.global.GProtocolDecl;
import org.scribble.codegen.java.JEndpointApiGenerator;
import org.scribble.codegen.java.callbackapi.CBEndpointApiGenerator3;
import org.scribble.core.job.Job;
import org.scribble.core.job.JobContext;
import org.scribble.core.job.JobArgs;
import org.scribble.core.lang.local.LProtocol;
import org.scribble.core.model.endpoint.EGraph;
import org.scribble.core.model.global.SGraph;
import org.scribble.core.type.name.GProtocolName;
import org.scribble.core.type.name.LProtocolName;
import org.scribble.core.type.name.Role;
import org.scribble.lang.Lang;
import org.scribble.lang.LangContext;
import org.scribble.main.Main;
import org.scribble.main.resource.locator.DirectoryResourceLocator;
import org.scribble.main.resource.locator.ResourceLocator;
import org.scribble.util.AntlrSourceException;
import org.scribble.util.RuntimeScribException;
import org.scribble.util.ScribException;
import org.scribble.util.ScribParserException;
import org.scribble.util.ScribUtil;

public class CommandLine
{
	protected final Map<CLArgFlag, String[]> args;  // Maps each flag to list of associated argument values

	protected CommandLine(CLArgParser p) throws CommandLineException
	{
		p.parse();
		this.args = p.getArgs();
	}

	public CommandLine(String... args) throws CommandLineException
	{
		//this.args = new CLArgParser(args).getArgs();
		this(new CLArgParser(args));
		if (!this.args.containsKey(CLArgFlag.MAIN_MOD)
				&& !this.args.containsKey(CLArgFlag.INLINE_MAIN_MOD))
		{
			throw new CommandLineException("No main module has been specified\r\n");
		}
	}

	// A Scribble extension should override newMainContext as appropriate.
	protected Main newMainContext()
			throws ScribParserException, ScribException
	{
		// FIXME: refactor into arg parsing
		boolean debug = this.args.containsKey(CLArgFlag.VERBOSE);  // TODO: factor out (cf. MainContext fields)
		boolean useOldWf = this.args.containsKey(CLArgFlag.OLD_WF);
		boolean noProgress = this.args.containsKey(CLArgFlag.NO_PROGRESS);
		boolean minEfsm = this.args.containsKey(CLArgFlag.LTSCONVERT_MIN);
		boolean fair = this.args.containsKey(CLArgFlag.FAIR);
		boolean noLocalChoiceSubjectCheck = 
				this.args.containsKey(CLArgFlag.NO_LOCAL_CHOICE_SUBJECT_CHECK);
		boolean noAcceptCorrelationCheck = 
				this.args.containsKey(CLArgFlag.NO_ACCEPT_CORRELATION_CHECK);
		boolean noValidation = this.args.containsKey(CLArgFlag.NO_VALIDATION);
		boolean spin = this.args.containsKey(CLArgFlag.SPIN);
		
		// FIXME: refactor into arg parsing
		Map<JobArgs, Boolean> args = new HashMap<>();
		args.put(JobArgs.DEBUG, debug);
		args.put(JobArgs.OLD_WF, useOldWf);
		args.put(JobArgs.NO_PROGRESS, noProgress);
		args.put(JobArgs.MIN_EFSM, minEfsm);
		args.put(JobArgs.FAIR, fair);
		args.put(JobArgs.NO_LCHOICE_SUBJ_CHECK, noLocalChoiceSubjectCheck);
		args.put(JobArgs.NO_ACC_CORRELATION_CHECK, noAcceptCorrelationCheck);
		args.put(JobArgs.NO_VALIDATION, noValidation);
		args.put(JobArgs.SPIN, spin);
		args = Collections.unmodifiableMap(args);

		List<Path> impaths = this.args.containsKey(CLArgFlag.IMPORT_PATH)
				? CommandLine.parseImportPaths(this.args.get(CLArgFlag.IMPORT_PATH)[0])
				: Collections.emptyList();
		if (this.args.containsKey(CLArgFlag.INLINE_MAIN_MOD))
		{
			String inline = this.args.get(CLArgFlag.INLINE_MAIN_MOD)[0];
			return new Main(inline, args);
		}
		else
		{
			ResourceLocator locator = new DirectoryResourceLocator(impaths);
			Path mainpath = CommandLine.parseMainPath(this.args.get(CLArgFlag.MAIN_MOD)[0]);
			return new Main(locator, mainpath, args);
		}
	}

	public static void main(String[] args)
			throws CommandLineException, AntlrSourceException
	{
		new CommandLine(args).run();
	}

	public void run() throws CommandLineException, AntlrSourceException  // ScribbleException is for JUnit testing
	{
		try
		{
			try
			{
				runBody();
			}
			catch (ScribException e)  // Wouldn't need to do this if not Runnable (so maybe change)
			{
				if (this.args.containsKey(CLArgFlag.JUNIT)
						|| this.args.containsKey(CLArgFlag.VERBOSE))
				{
					/*RuntimeScribbleException ee = new RuntimeScribbleException(e.getMessage());
					ee.setStackTrace(e.getStackTrace());
					throw ee;*/
					throw e;
				}
				else
				{
					System.err.println(e.getMessage());  // JUnit harness looks for an exception
					System.exit(1);
				}
			}
		}
		catch (ScribParserException | CommandLineException e)
		{
			System.err.println(e.getMessage());  // No need to give full stack trace, even for debug, for command line errors
			System.exit(1);
		}
		catch (RuntimeScribException e)
		{
			System.err.println(e.getMessage());
			System.exit(1);
		}
	}

	protected void runBody()
			throws ScribException, ScribParserException, AntlrSourceException, CommandLineException
	{
		Main mc = newMainContext();  // Represents current instance of tooling for given CL args
		Lang lang = mc.newLang();  // A Job is some series of passes performed on each Module in the MainContext (e.g., cf. Job::runVisitorPass)
		ScribException fail = null;
		try
		{
			doValidationTasks(lang);  // FIXME: refactor into job
		}
		catch (ScribException x)
		{
			fail = x;
		}
		
		// Attempt certain "output tasks" even if above failed, in case can still do some useful output (hacky)
		try
		{
			tryOutputTasks(lang);  // FIXME: refactor into job
		}
		catch (ScribException x)
		{
			if (fail == null)
			{
				fail = x;
			}
		}

		if (fail != null)  // Well-formedness check and/or an "attemptable output task" failed
		{
			throw fail;
		}

		// "Non-attemptable" output tasks: should not attempt these if any previous failure
		doNonAttemptableOutputTasks(lang);
	}

	// AntlrSourceException super of ScribbleException -- needed for, e.g., AssrtCoreSyntaxException
	protected void doValidationTasks(Lang lang) 
			throws AntlrSourceException, ScribParserException,  // Latter in case needed by subclasses
				CommandLineException
	{
		/*// Scribble extensions (custom Job passes)
		if (this.args.containsKey(F17CLArgFlag.F17))
		{
			GProtocolName simpname = new GProtocolName(this.args.get(ArgFlag.F17)[0]);
			F17Main.parseAndCheckWF(lang, simpname);  // Includes base passes
		}

		// Base Scribble
		else*/
		{
			lang.runPasses();  // TODO: refactor, w.r.t. below
			lang.toJob().checkWellFormedness();
		}
	
	}

	protected void tryOutputTasks(Lang lang)
			throws CommandLineException, ScribException
	{
		// Following must be ordered appropriately -- ?
		if (this.args.containsKey(CLArgFlag.PROJECT))
		{
			printProjections(lang);
		}
		if (this.args.containsKey(CLArgFlag.EFSM))
		{
			printEGraph(lang, true, true);
		}
		if (this.args.containsKey(CLArgFlag.VALIDATION_EFSM))
		{
			printEGraph(lang, false, true);
		}
		if (this.args.containsKey(CLArgFlag.UNFAIR_EFSM))
		{
			printEGraph(lang, false, false);
		}
		if (this.args.containsKey(CLArgFlag.EFSM_PNG))
		{
			drawEGraph(lang, true, true);
		}
		if (this.args.containsKey(CLArgFlag.VALIDATION_EFSM_PNG))
		{
			drawEGraph(lang, false, true);
		}
		if (this.args.containsKey(CLArgFlag.UNFAIR_EFSM_PNG))
		{
			drawEGraph(lang, false, false);
		}
		if (this.args.containsKey(CLArgFlag.SGRAPH)
				|| this.args.containsKey(CLArgFlag.SGRAPH_PNG)
				|| this.args.containsKey(CLArgFlag.UNFAIR_SGRAPH)
				|| this.args.containsKey(CLArgFlag.UNFAIR_SGRAPH_PNG))
		{
			if (lang.config.args.get(JobArgs.OLD_WF))
			{
				throw new CommandLineException(
						"Global model flag(s) incompatible with: "
								+ CLArgParser.OLD_WF_FLAG);
			}
			if (this.args.containsKey(CLArgFlag.SGRAPH))
			{
				printSGraph(lang, true);
			}
			if (this.args.containsKey(CLArgFlag.UNFAIR_SGRAPH))
			{
				printSGraph(lang, false);
			}
			if (this.args.containsKey(CLArgFlag.SGRAPH_PNG))
			{
				drawSGraph(lang, true);
			}
			if (this.args.containsKey(CLArgFlag.UNFAIR_SGRAPH_PNG))
			{
				drawSGraph(lang, false);
			}
		}
	}

	// TODO: rename
	protected void doNonAttemptableOutputTasks(Lang lang)
			throws ScribException, CommandLineException
	{
		if (this.args.containsKey(CLArgFlag.SESS_API_GEN))
		{
			outputSessionApi(lang);
		}
		if (this.args.containsKey(CLArgFlag.SCHAN_API_GEN))
		{
			outputStateChannelApi(lang);
		}
		if (this.args.containsKey(CLArgFlag.API_GEN))
		{
			outputEndpointApi(lang);
		}
		if (this.args.containsKey(CLArgFlag.ED_API_GEN))
		{
			outputEventDrivenApi(lang);
		}
	}

	// TODO: option to write to file, like classes
	private void printProjections(Lang lang)
			throws CommandLineException, ScribException
	{
		LangContext jobc = lang.getContext();
		Job job = lang.toJob();
		String[] args = this.args.get(CLArgFlag.PROJECT);
		for (int i = 0; i < args.length; i += 2)
		{
			GProtocolName fullname = checkGlobalProtocolArg(jobc, args[i]);
			Role role = checkRoleArg(jobc, fullname, args[i+1]);
			Map<LProtocolName, LProtocol> projections = job.getProjections(fullname,
					role);  // FIXME: output Module
			System.out.println("\n" + projections.values().stream()
					.map(p -> p.toString()).collect(Collectors.joining("\n\n")));
		}
	}

	// dot/aut text output
	// forUser: true means for API gen and general user info (may be minimised), false means for validation (non-minimised, fair or unfair)
	// (forUser && !fair) should not hold, i.e. unfair doesn't make sense if forUser
	private void printEGraph(Lang lang, boolean forUser, boolean fair)
			throws ScribException, CommandLineException
	{
		LangContext jobc = lang.getContext();
		String[] args = forUser 
				? this.args.get(CLArgFlag.EFSM)
				: (fair 
						? this.args.get(CLArgFlag.VALIDATION_EFSM)
						: this.args.get(CLArgFlag.UNFAIR_EFSM));
		for (int i = 0; i < args.length; i += 2)
		{
			GProtocolName fullname = checkGlobalProtocolArg(jobc, args[i]);
			Role role = checkRoleArg(jobc, fullname, args[i+1]);
			EGraph fsm = getEGraph(lang, fullname, role, forUser, fair);
			String out = this.args.containsKey(CLArgFlag.AUT) 
					? fsm.toAut()
					: fsm.toDot();
			System.out.println("\n" + out);  // Endpoint graphs are "inlined" (a single graph is built)
		}
	}

	private void drawEGraph(Lang lang, boolean forUser, boolean fair)
			throws ScribException, CommandLineException
	{
		LangContext jobc = lang.getContext();
		String[] args = forUser 
				? this.args.get(CLArgFlag.EFSM_PNG)
				: (fair 
						? this.args.get(CLArgFlag.VALIDATION_EFSM_PNG)
						: this.args.get(CLArgFlag.UNFAIR_EFSM_PNG));
		for (int i = 0; i < args.length; i += 3)
		{
			GProtocolName fullname = checkGlobalProtocolArg(jobc, args[i]);
			Role role = checkRoleArg(jobc, fullname, args[i+1]);
			String png = args[i+2];
			EGraph fsm = getEGraph(lang, fullname, role, forUser, fair);
			runDot(fsm.toDot(), png);
		}
	}

  // Endpoint graphs are "inlined", so only a single graph is built (cf. projection output)
	private EGraph getEGraph(Lang lang, GProtocolName fullname, Role role,
			boolean forUser, boolean fair)
			throws ScribException, CommandLineException
	{
		LangContext jobc = lang.getContext();
		JobContext jobc2 = lang.toJob().getContext();
		GProtocolDecl gpd = (GProtocolDecl) jobc.getMainModule()
				.getProtocolDeclChild(fullname.getSimpleName());
		if (gpd == null || !gpd.getHeaderChild().getRoleDeclListChild().getRoles()
				.contains(role))
		{
			throw new CommandLineException("Bad FSM construction args: "
					+ Arrays.toString(this.args.get(CLArgFlag.DOT)));
		}
		EGraph graph;
		if (forUser)  // The (possibly minimised) user-output EFSM for API gen
		{
			graph = this.args.containsKey(CLArgFlag.LTSCONVERT_MIN)
					? jobc2.getMinimisedEGraph(fullname, role)
					: jobc2.getEGraph(fullname, role);
		}
		else  // The (possibly unfair-transformed) internal EFSM for validation
		{
			graph = //(!this.args.containsKey(ArgFlag.FAIR) && !this.args.containsKey(ArgFlag.NO_LIVENESS))  // Cf. GlobalModelChecker.getEndpointFSMs
					!fair
					? jobc2.getUnfairEGraph(fullname, role) 
					: jobc2.getEGraph(fullname, role);
		}
		if (graph == null)
		{
			throw new RuntimeScribException("Shouldn't see this: " + fullname);
					// Should be suppressed by an earlier failure
		}
		return graph;
	}

	private void printSGraph(Lang lang, boolean fair)
			throws ScribException, CommandLineException
	{
		LangContext jobc = lang.getContext();
		String[] args = fair 
				? this.args.get(CLArgFlag.SGRAPH)
				: this.args.get(CLArgFlag.UNFAIR_SGRAPH);
		for (int i = 0; i < args.length; i += 1)
		{
			GProtocolName fullname = checkGlobalProtocolArg(jobc, args[i]);
			SGraph model = getSGraph(lang, fullname, fair);
			String out = this.args.containsKey(CLArgFlag.AUT) 
					? model.toAut()
					: model.toDot();
			System.out.println("\n" + out);
		}
	}

	private void drawSGraph(Lang lang, boolean fair)
			throws ScribException, CommandLineException
	{
		LangContext jobc = lang.getContext();
		String[] args = fair 
				? this.args.get(CLArgFlag.SGRAPH_PNG)
				: this.args.get(CLArgFlag.UNFAIR_SGRAPH_PNG);
		for (int i = 0; i < args.length; i += 2)
		{
			GProtocolName fullname = checkGlobalProtocolArg(jobc, args[i]);
			String png = args[i+1];
			SGraph model = getSGraph(lang, fullname, fair);
			runDot(model.toDot(), png);
		}
	}

	private static SGraph getSGraph(Lang lang, GProtocolName fullname, boolean fair)
			throws ScribException
	{
		JobContext jobc2 = lang.toJob().getContext();
		SGraph model = fair 
				? jobc2.getSGraph(fullname)
				: jobc2.getUnfairSGraph(fullname);
		if (model == null)
		{
			throw new RuntimeScribException("Shouldn't see this: " + fullname);
					// Should be suppressed by an earlier failure
		}
		return model;
	}

	private void outputEndpointApi(Lang lang)
			throws ScribException, CommandLineException
	{
		LangContext jobc = lang.getContext();
		String[] args = this.args.get(CLArgFlag.API_GEN);
		JEndpointApiGenerator jgen = new JEndpointApiGenerator(lang);  // FIXME: refactor (generalise -- use new API)
		for (int i = 0; i < args.length; i += 2)
		{
			GProtocolName fullname = checkGlobalProtocolArg(jobc, args[i]);
			Map<String, String> sessClasses = jgen.generateSessionApi(fullname);
			outputClasses(sessClasses);
			Role role = checkRoleArg(jobc, fullname, args[i+1]);
			Map<String, String> scClasses = jgen.generateStateChannelApi(fullname,
					role, this.args.containsKey(CLArgFlag.SCHAN_API_SUBTYPES));
			outputClasses(scClasses);
		}
	}

	private void outputSessionApi(Lang lang)
			throws ScribException, CommandLineException
	{
		LangContext jobc = lang.getContext();
		String[] args = this.args.get(CLArgFlag.SESS_API_GEN);
		JEndpointApiGenerator jgen = new JEndpointApiGenerator(lang);  // TODO: refactor (generalise -- use new API)
		for (String fullname : args)
		{
			GProtocolName gpn = checkGlobalProtocolArg(jobc, fullname);
			Map<String, String> classes = jgen.generateSessionApi(gpn);
			outputClasses(classes);
		}
	}

	private void outputStateChannelApi(Lang lang)
			throws ScribException, CommandLineException
	{
		LangContext jobc = lang.getContext();
		String[] args = this.args.get(CLArgFlag.SCHAN_API_GEN);
		JEndpointApiGenerator jgen = new JEndpointApiGenerator(lang);  // TODO: refactor (generalise -- use new API)
		for (int i = 0; i < args.length; i += 2)
		{
			GProtocolName fullname = checkGlobalProtocolArg(jobc, args[i]);
			Role self = checkRoleArg(jobc, fullname, args[i+1]);
			Map<String, String> classes = jgen.generateStateChannelApi(fullname, self,
					this.args.containsKey(CLArgFlag.SCHAN_API_SUBTYPES));
			outputClasses(classes);
		}
	}

	private void outputEventDrivenApi(Lang lang)
			throws ScribException, CommandLineException
	{
		LangContext jobc = lang.getContext();
		String[] args = this.args.get(CLArgFlag.ED_API_GEN);
		/*JEndpointApiGenerator jgen = new JEndpointApiGenerator(lang);  // FIXME: refactor (generalise -- use new API)
		for (int i = 0; i < args.length; i += 2)
		{
			GProtocolName fullname = checkGlobalProtocolArg(jobc, args[i]);
			Map<String, String> sessClasses = jgen.generateSessionApi(fullname);
			outputClasses(sessClasses);
			Role role = checkRoleArg(jobc, fullname, args[i+1]);
			Map<String, String> scClasses = jgen.generateStateChannelApi(fullname, role, this.args.containsKey(CLArgFlag.SCHAN_API_SUBTYPES));
			outputClasses(scClasses);
		}*/
		for (int i = 0; i < args.length; i += 2)
		{
			GProtocolName fullname = checkGlobalProtocolArg(jobc, args[i]);
			Role self = checkRoleArg(jobc, fullname, args[i+1]);
			CBEndpointApiGenerator3 edgen = new CBEndpointApiGenerator3(lang, fullname,
					self, this.args.containsKey(CLArgFlag.SCHAN_API_SUBTYPES));
			Map<String, String> out = edgen.build();
			outputClasses(out);
		}
	}

	// filepath -> class source
	protected void outputClasses(Map<String, String> classes)
			throws ScribException
	{
		Consumer<String> f;
		if (this.args.containsKey(CLArgFlag.API_OUTPUT))
		{
			String dir = this.args.get(CLArgFlag.API_OUTPUT)[0];
			f = path -> { ScribUtil.handleLambdaScribbleException(() ->
							{
								String tmp = dir + "/" + path;
								if (this.args.containsKey(CLArgFlag.VERBOSE))
								{
									System.out.println("[DEBUG] Writing to: " + tmp);
								}
								ScribUtil.writeToFile(tmp, classes.get(path)); return null;
							}); };
		}
		else
		{
			f = path -> { System.out.println(path + ":\n" + classes.get(path)); };
		}
		classes.keySet().stream().forEach(f);
	}

	protected static void runDot(String dot, String png)
			throws ScribException, CommandLineException
	{
		String tmpName = png + ".tmp";
		File tmp = new File(tmpName);
		if (tmp.exists())
		{
			throw new CommandLineException("Cannot overwrite: " + tmpName);
		}
		try
		{
			ScribUtil.writeToFile(tmpName, dot);
			String[] res = ScribUtil.runProcess("dot", "-Tpng", "-o" + png, tmpName);
			System.out.print(!res[1].isEmpty() ? res[1] : res[0]);  // already "\n" terminated
		}
		finally
		{
			tmp.delete();
		}
	}

	protected static Path parseMainPath(String path)
	{
		return Paths.get(path);
	}

	protected static List<Path> parseImportPaths(String paths)
	{
		return Arrays.stream(paths.split(File.pathSeparator)).map(s -> Paths.get(s))
				.collect(Collectors.toList());
	}

	protected static GProtocolName checkGlobalProtocolArg(LangContext jobc,
			String simpname) throws CommandLineException
	{
		GProtocolName simpgpn = new GProtocolName(simpname);
		Module main = jobc.getMainModule();
		if (!main.hasProtocolDecl(simpgpn))
		{
			throw new CommandLineException("Global protocol not found: " + simpname);
		}
		ProtocolDecl<?> pd = main.getProtocolDeclChild(simpgpn);
		if (pd == null || !pd.isGlobal())
		{
			throw new CommandLineException("Global protocol not found: " + simpname);
		}
		if (pd.isAux())  // CHECKME: maybe don't check for all, e.g. -project
		{
			throw new CommandLineException(
					"Invalid aux protocol specified as root: " + simpname);
		}
		return new GProtocolName(jobc.lang.config.main, simpgpn);  // TODO: take Job param instead of Jobcontext
	}

	protected static Role checkRoleArg(LangContext jobc,
			GProtocolName fullname, String rolename) throws CommandLineException
	{
		ProtocolDecl<?> pd = jobc.getMainModule()
				.getProtocolDeclChild(fullname.getSimpleName());
		Role role = new Role(rolename);
		if (!pd.getHeaderChild().getRoleDeclListChild().getRoles().contains(role))
		{
			throw new CommandLineException(
					"Role not declared for " + fullname + ": " + role);
		}
		return role;
	}
}
