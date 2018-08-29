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
package org.scribble.del.global;

import java.io.File;
import java.io.IOException;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import org.scribble.ast.AstFactory;
import org.scribble.ast.Module;
import org.scribble.ast.NonRoleParamDeclList;
import org.scribble.ast.RoleDeclList;
import org.scribble.ast.ScribNode;
import org.scribble.ast.context.DependencyMap;
import org.scribble.ast.context.global.GProtocolDeclContext;
import org.scribble.ast.global.GProtocolDecl;
import org.scribble.ast.global.GProtocolHeader;
import org.scribble.ast.local.LProtocolDecl;
import org.scribble.ast.local.LProtocolDef;
import org.scribble.ast.local.LProtocolHeader;
import org.scribble.ast.name.qualified.LProtocolNameNode;
import org.scribble.del.ModuleDel;
import org.scribble.del.ProtocolDeclDel;
import org.scribble.main.Job;
import org.scribble.main.JobContext;
import org.scribble.main.ScribbleException;
import org.scribble.model.MState;
import org.scribble.model.endpoint.EGraph;
import org.scribble.model.endpoint.EState;
import org.scribble.model.endpoint.EStateKind;
import org.scribble.model.global.SGraph;
import org.scribble.type.kind.Global;
import org.scribble.type.name.GProtocolName;
import org.scribble.type.name.MessageId;
import org.scribble.type.name.ProtocolName;
import org.scribble.type.name.Role;
import org.scribble.util.ScribUtil;
import org.scribble.visit.context.Projector;
import org.scribble.visit.context.ProtocolDeclContextBuilder;
import org.scribble.visit.context.env.ProjectionEnv;
import org.scribble.visit.util.MessageIdCollector;
import org.scribble.visit.util.RoleCollector;
import org.scribble.visit.validation.GProtocolValidator;

public class GProtocolDeclDel extends ProtocolDeclDel<Global>
{
	public GProtocolDeclDel()
	{

	}
	
	@Override
	public GProtocolDeclContext getProtocolDeclContext()
	{
		return (GProtocolDeclContext) super.getProtocolDeclContext();
	}

	@Override
	protected GProtocolDeclDel copy()
	{
		return new GProtocolDeclDel();
	}

	@Override
	protected void addSelfDependency(ProtocolDeclContextBuilder builder, ProtocolName<?> proto, Role role)
	{
		builder.addGlobalProtocolDependency(role, (GProtocolName) proto, role);
	}
	
	@Override
	public GProtocolDecl
			leaveProtocolDeclContextBuilding(ScribNode parent, ScribNode child, ProtocolDeclContextBuilder builder, ScribNode visited) throws ScribbleException
	{
		GProtocolDecl gpd = (GProtocolDecl) visited;
		GProtocolDeclContext gcontext = new GProtocolDeclContext(builder.getGlobalProtocolDependencyMap());
		GProtocolDeclDel del = (GProtocolDeclDel) setProtocolDeclContext(gcontext);
		return (GProtocolDecl) gpd.del(del);
	}

	@Override
	public ScribNode leaveRoleCollection(ScribNode parent, ScribNode child, RoleCollector coll, ScribNode visited) throws ScribbleException
	{
		GProtocolDecl gpd = (GProtocolDecl) visited;

		// Need to do here (e.g. RoleDeclList too early, def not visited yet)
		// Currently only done for global, local does roledecl fixing after role collection -- should separate this check to a later pass after context building
		// Maybe relax to check only occs.size() > 1
		List<Role> decls = gpd.header.roledecls.getRoles();
		Set<Role> occs = coll.getNames();
		if (occs.size() != decls.size()) 
		{
			decls.removeAll(occs);
			throw new ScribbleException(gpd.header.roledecls.getSource(), "Unused role decl(s) in " + gpd.header.name + ": " + decls);
		}

		return super.leaveRoleCollection(parent, child, coll, gpd);
	}

	@Override
	public GProtocolDecl
			leaveProjection(ScribNode parent, ScribNode child, Projector proj, ScribNode visited) throws ScribbleException
	{
		AstFactory af = proj.job.af;

		Module root = proj.job.getContext().getModule(proj.getModuleContext().root);
		GProtocolDecl gpd = (GProtocolDecl) visited;
		GProtocolHeader gph = gpd.getHeader();
		Role self = proj.peekSelf();

		LProtocolNameNode pn = Projector.makeProjectedSimpleNameNode(af, gph.getSource(), gph.getDeclName(), self);
		RoleDeclList roledecls = gph.roledecls.project(af, self);
		NonRoleParamDeclList paramdecls = gph.paramdecls.project(af, self);
		//LProtocolHeader hdr = af.LProtocolHeader(gpd.header.getSource(), pn, roledecls, paramdecls);  // FIXME: make a header del and move there?
		LProtocolHeader hdr = gph.project(af, self, pn, roledecls, paramdecls);
		LProtocolDef def = (LProtocolDef) ((ProjectionEnv) gpd.def.del().env()).getProjection();
		LProtocolDecl lpd = gpd.project(af, root, self, hdr, def);  // FIXME: is root (always) the correct module? (wrt. LProjectionDeclDel?)
		
		Map<GProtocolName, Set<Role>> deps = ((GProtocolDeclDel) gpd.del()).getGlobalProtocolDependencies(self);
		Module projected = ((ModuleDel) root.del()).createModuleForProjection(proj, root, gpd, lpd, deps);
		proj.addProjection(gpd.getFullMemberName(root), self, projected);
		return gpd;
	}

	protected Map<GProtocolName, Set<Role>> getGlobalProtocolDependencies(Role self)
	{
		DependencyMap<GProtocolName> deps = getProtocolDeclContext().getDependencyMap();
		return deps.getDependencies().get(self);
	}
	
	@Override
	public void enterValidation(ScribNode parent, ScribNode child, GProtocolValidator checker) throws ScribbleException
	{
		GProtocolDecl gpd = (GProtocolDecl) child;
		if (gpd.isAuxModifier())
		{
			return;
		}

		GProtocolName fullname = gpd.getFullMemberName((Module) parent);
		if (checker.job.spin)
		{
			/*if (checker.job.fair)
			{
				throw new RuntimeException("[TODO]: -spin currently does not support fair ouput choices.");
			}*/
			validateBySpin(checker.job, fullname, checker.job.fair);
		}
		else
		{
			validateByScribble(checker.job, fullname, true);
			if (!checker.job.fair)
			{
				checker.job.debugPrintln("(" + fullname + ") Validating with \"unfair\" output choices.. ");
				validateByScribble(checker.job, fullname, false);  // FIXME: only need to check progress, not full validation
			}
		}
	}

	private static void validateByScribble(Job job, GProtocolName fullname, boolean fair) throws ScribbleException
	{
		JobContext jc = job.getContext();
		SGraph graph = (fair) ? jc.getSGraph(fullname) : jc.getUnfairSGraph(fullname);
		//graph.toModel().validate(job);
		job.sf.newSModel(graph).validate(job);
	}
	
	private static String getPmlLabel(Role r, EState s)  // FIXME: factor out with EGraph.toPml
	{
		return (s.getStateKind() == EStateKind.TERMINAL)
				? "end" + r + s.id
				: "label" + r + s.id;
	}
		
	private static void validateBySpin(Job job, GProtocolName fullname, boolean fair) throws ScribbleException
	{
		JobContext jc = job.getContext();
		Module mod = jc.getModule(fullname.getPrefix());
		GProtocolDecl gpd = (GProtocolDecl) mod.getProtocolDecl(fullname.getSimpleName());
		
		List<Role> rs = gpd.header.roledecls.getRoles().stream()
				.sorted(Comparator.comparing(Role::toString)).collect(Collectors.toList());

		MessageIdCollector coll = new MessageIdCollector(job, ((ModuleDel) mod.del()).getModuleContext());
		gpd.accept(coll);
		Set<MessageId<?>> mids = coll.getNames();
		
		String pml = "";
		pml += "mtype {" + mids.stream().map(mid -> mid.toString()).collect(Collectors.joining(", ")) + "};\n";

		// FIXME: explicit

		pml += "\n";
		List<Role[]> pairs = new LinkedList<>();
		/*for (Role r1 : rs)
		{
			for (Role r2 : rs)
			{
				if (!r1.equals(r2))
				{
					pairs.add(new Role[] {r1, r2});
				}
			}
		}*/
		pairs = rs.stream()
				.flatMap(r1 -> rs.stream().flatMap(r2 -> !r1.equals(r2) ? Stream.<Role[]>of(new Role[]{r1, r2}) : Stream.<Role[]>empty()))
				.collect(Collectors.toList());
		//for (Role[] p : (Iterable<Role[]>) () -> pairs.stream().sorted().iterator())
		for (Role[] p : pairs)  // FIXME: use a single chan, half-duplex?
		{
			pml += "chan s_" + p[0] + "_" + p[1] + " = [1] of { mtype };\n"  
								// Async queue size 1 even though separate s/r chans, to work with guarded inputs
								// But this interferes with 1-bounded (2-bounded?), and eventual stability?
					 //+ "chan r_" + p[0] + "_" + p[1] + " = [1] of { mtype };\n"
					 + "bool empty_" + p[0] + "_" + p[1] + " = true;\n"
					 /*+ "active proctype chan_" + p[0] + "_" + p[1] + "() {\n"
					 + "mtype m;\n"
					 + "end_chan_" + p[0] + "_" + p[1] + ":\n"
					 + "do\n"
					 + "::\n"
					 + "atomic { s_" + p[0] + "_" + p[1] + "?m; empty_" + p[0] + "_" + p[1] + " = false }\n"
					 + "atomic { r_" + p[0] + "_" + p[1] + "!m; empty_" + p[0] + "_" + p[1] + " = true }\n"
					 + "od\n"
					 + "}\n"*/
					 ;
		}
		
		Map<Role, EGraph> gs = new HashMap<>();
		//rs.forEach(r -> egraphs.put(r, jc.getEGraph(fullname, r)));  // getEGraph throws exception
		for (Role r : rs)
		{
			EGraph g = jc.getEGraph(fullname, r);
			gs.put(r, g);
			pml += "\n\n" + g.toPml(r);
			if (job.debug)
			{
				System.out.println("[-spin]: Promela processes\n" + pml + "\n");
			}
		}
		
	// FIXME split termination-fairness and non-terminating-fairness
		boolean termFair = gs.values().stream().allMatch(g -> g.isTermFair());
		if (fair)
		{
			if (termFair)
			{
				validateBySpinTermFair(job, fullname, gpd, rs, pairs, pml, true);
			}
			else
			{
				validateBySpinNonTermFair(job, fullname, gpd, rs, pairs, pml, true);
			}
		}
		else
		{
			validateBySpinNonTermFair(job, fullname, gpd, rs, pairs, pml, false);
		}
	}

	
	// FIXME: integrate with below -- currently this is not used with fair==false
	private static void validateBySpinTermFair(Job job, GProtocolName fullname, GProtocolDecl gpd,
			List<Role> rs, List<Role[]> pairs, String pml, boolean fair) throws ScribbleException
	{
		JobContext jc = job.getContext();

		List<String> fairChoices = new LinkedList<>();  // Poly-output only
		List<String> clauses = new LinkedList<>();
		for (Role r : rs)
		{

			// FIXME: factor out with above
			Set<EState> tmp = new HashSet<>();
			EGraph g = jc.getEGraph(fullname, r);
			tmp.add(g.init);
			tmp.addAll(MState.getReachableStates(g.init));

			if (g.term != null)
			{
				clauses.add(r + "@" + getPmlLabel(r, g.term));
				tmp.remove(g.term);
			}
			tmp.forEach(s ->  // Throws exception, cannot use flatMap
			{
				EStateKind kind = s.getStateKind();
				if (kind == EStateKind.UNARY_INPUT || kind == EStateKind.POLY_INPUT)  // FIXME: include outputs due to bounded model?  or subsumed by eventual stability
				{
					//clauses.add("!<>[]" + r + "@" + getPmlLabel(r, s));  // FIXME: factor out label
				}
				else if (kind != EStateKind.OUTPUT && kind != EStateKind.TERMINAL)
				{
					throw new RuntimeException("[-spin] TODO: " + kind);
				}
				if (fair && !s.getLabels().isEmpty())  // CHECKME: looking for recursion "entry" states
				{
					List<EState> ss = s.getSuccessors().stream().distinct().collect(Collectors.toList());
					if (kind == EStateKind.OUTPUT && ss.size() > 1)  // Latter clause redundant for fair-term?
					{
						fairChoices.add("!" + r + "@" + getPmlLabel(r, s));  // FIXME: factor out label
					}
				}
			});
		}
		String eventualStability = "";
		for (Role[] p : pairs)
		{
			eventualStability += (((eventualStability.isEmpty()) ? "" : " && ") + "empty_" + p[0] + "_" + p[1]);  // "eventual reception", not eventual stability
					// FIXME: eventual stability too strong -- can be violated by certain interleavings keeping alternate queues non-empty
					// N.B. "fairness" fixes the above for recursions-with-exits, since exit always eventually taken (so, eventual stable termination)
		}
		clauses.add(eventualStability);

		Map<String, String> props = new HashMap<>();
		int batchSize = 999999;  // FIXME: remove batching, redundant here
		for (int i = 0, k = 1; i < clauses.size(); k++)
		{
			int j = (i+batchSize < clauses.size()) ? i+batchSize : clauses.size();
			String batch = "<>[](" + clauses.subList(i, j).stream().collect(Collectors.joining(" && ")) + ")";
			String ltl =
					  "ltl p" + k + " {\n"
					+ ((fair && !fairChoices.isEmpty()) ? "<>[](" + fairChoices.stream().map(c -> c.toString()).collect(Collectors.joining(" && ")) + ")\n->\n" : "")  // FIXME: filter by batching? -- optimise batches more "semantically"?
							// OK, a -> (b && c) = (a -> b) && (a -> c)
					//+ "(" + batch + ")"
					+ batch
					+ "\n" + "}";
			if (job.debug)
			{
				System.out.println("[-spin] Batched ltl:\n" + ltl + "\n");
			}

			props.put("p" + k, ltl);  // Factour out prop name

			i += batchSize;
		}

		pml += props.values().stream().map(v -> "\n\n" + v).collect(Collectors.joining(""));
		if (!runSpin(job, fullname.toString(), pml, props.keySet().stream().collect(Collectors.toList())))
		{
			throw new ScribbleException("Protocol not valid:\n" + gpd);
		}
	}
		
	// for non-terminating-fairness, look for "recursion-entry" states to terminal sets and only do fairness on there?  will be faster except for nested and fat recursive-choices
	// FIXME: above needs restricting to such cases; "offset" recursive-choices are possible e.g., rec X { ...; ( A->B.X + A->B.end ) } -- no: should be OK?  only need to detect fairness via any action in each choice path, not necessarily the "entry" action)
	// eventual reception (for non-terminating-fairness) -- use batching, sound to batch by distribution-law for implies
	private static void validateBySpinNonTermFair(Job job, GProtocolName fullname, GProtocolDecl gpd,
			List<Role> rs, List<Role[]> pairs, String pml, boolean fair) throws ScribbleException
	{
		JobContext jc = job.getContext();

		List<String> fairChoices = new LinkedList<>();  // Poly-output only
		List<String> clauses = new LinkedList<>();  // Conjunction
		for (Role r : rs)
		{
			Set<EState> tmp = new HashSet<>();
			EGraph g = jc.getEGraph(fullname, r);
			tmp.add(g.init);
			tmp.addAll(MState.getReachableStates(g.init));
			if (g.term != null)
			{
				tmp.remove(g.term);
			}
			tmp.forEach(s ->  // Throws exception, cannot use flatMap
			{
				EStateKind kind = s.getStateKind();
				if (kind == EStateKind.UNARY_INPUT || kind == EStateKind.POLY_INPUT)  // FIXME: include outputs due to bounded model?  or subsumed by eventual stability
				{
					clauses.add("<>!" + r + "@" + getPmlLabel(r, s));  // [] will be added to whole batch  // FIXME: factor out label
				}
				else if (kind != EStateKind.OUTPUT && kind != EStateKind.TERMINAL)
				{
					throw new RuntimeException("[-spin] TODO: " + kind);
				}
				if (fair)
				{
					List<EState> ss = s.getSuccessors().stream().distinct().collect(Collectors.toList());
					if (kind == EStateKind.OUTPUT && ss.size() > 1)  // FIXME: broken for multiple actions to same successor, e.g., rec X { A->B.X + A->C.X }
					{
						fairChoices.add("([]<>" + r + "@" + getPmlLabel(r, s) + " -> [](" 
								+ ss.stream().map(succ -> "<>" + r + "@" + getPmlLabel(r, succ)).collect(Collectors.joining(" && "))
								+ "))");  // FIXME: factor out label
					}
				}
			});
		}
		//*/
		/*String roleProgress = "";  // This way is not faster
		for (Role r : rs)
		{
			Set<EState> tmp = new HashSet<>();
			EGraph g = jc.getEGraph(fullname, r);
			tmp.add(g.init);
			tmp.addAll(MState.getReachableStates(g.init));
			if (g.term != null)
			{
				tmp.remove(g.term);
			}
			roleProgress += (((roleProgress.isEmpty()) ? "" : " || ")
					+ tmp.stream().map(s -> r + "@label" + r + s.id).collect(Collectors.joining(" || ")));
		}
		roleProgress = "!<>[](" + roleProgress + ")";
		clauses.add(roleProgress);*/
		/*for (Role[] p : pairs)
		{
			clauses.add("[]<>(empty_" + p[0] + "_" + p[1] + ")");
		}*/
		//String eventualStability = "";
		for (Role[] p : pairs)
		{
			/*eventualStability += (((eventualStability.isEmpty()) ? "" : " && ") + "<>empty_" + p[0] + "_" + p[1]);  // "eventual reception", not eventual stability
			//eventualStability += (((eventualStability.isEmpty()) ? "" : " && ") + "empty_" + p[0] + "_" + p[1]);
					// FIXME: eventual stability too strong -- can be violated by certain interleavings keeping alternate queues non-empty
					// N.B. "fairness" fixes the above for recursions-with-exits, since exit always eventually taken (so, eventual stable termination)*/
			String eventualReception = "<>empty_" + p[0] + "_" + p[1];  // [] will be added to whole batch
			clauses.add(eventualReception);
		}
		/*eventualStability = "[](" + eventualStability + ")";
		//eventualStability = "[]<>(" + eventualStability + ")";
		clauses.add(eventualStability);*/

		Map<String, String> props = new HashMap<>();
		//int batchSize = 10;  // FIXME: factor out
		int batchSize = 2;  // FIXME: factor out  
				// FIXME: dynamic batch sizing based on previous batch duration?  
				// CHECKME: batching better for error reporting?  (batchSize=1 best?)
		for (int i = 0, k = 1; i < clauses.size(); k++)
		{
			int j = (i+batchSize < clauses.size()) ? i+batchSize : clauses.size();
			String batch = "[](" + clauses.subList(i, j).stream().collect(Collectors.joining(" && ")) + ")";
			String ltl =
					  "ltl p" + k + " {\n"
					+ ((fair && !fairChoices.isEmpty()) ? "(" + fairChoices.stream().map(c -> c.toString()).collect(Collectors.joining(" && ")) + ")\n->\n" : "")  // FIXME: filter by batching? -- optimise batches more "semantically"?
					+ "(" + batch + ")"
					+ "\n" + "}";
			if (job.debug)
			{
				System.out.println("[-spin] Batched ltl:\n" + ltl + "\n");
			}
			/*if (!runSpin(fullname.toString(), pml + "\n\n" + ltl))
			{
				throw new ScribbleException("Protocol not valid:\n" + gpd);
			}*/

			props.put("p" + k, ltl);  // Factour out prop name

			i += batchSize;
		}

		/*String ltl =
					"ltl {\n"
				+ ((fair && !fairChoices.isEmpty()) ? "(" + fairChoices.stream().map(c -> c.toString()).collect(Collectors.joining(" && ")) + ") ->" : "")  // FIXME: filter by batching? -- optimise batches more "semantically"?
				+ "\n"
				+ "(" + eventualStability + ")"
				+ "\n" + "}";*/
		pml += props.values().stream().map(v -> "\n\n" + v).collect(Collectors.joining(""));
		/*if (job.debug)
		{
			System.out.println("[-spin] Eventual stability:\n" + ltl + "\n");
		}*/
		if (!runSpin(job, fullname.toString(), pml, props.keySet().stream().collect(Collectors.toList())))
		{
			throw new ScribbleException("Protocol not valid:\n" + gpd);
		}
	}

	// FIXME: move
	private static boolean runSpin(Job job, String prefix, String pml, List<String> props) //throws ScribbleException
	{
		File tmp;
		try
		{
			tmp = File.createTempFile(prefix, ".pml.tmp");
			try
			{
				String tmpName = tmp.getAbsolutePath();				
				ScribUtil.writeToFile(tmpName, pml);
				String[] res = ScribUtil.runProcess("spin", "-a", tmpName);
				res[0] = res[0].replaceAll("(?m)^ltl.*$", "");
				res[0] = res[0].replaceAll("(?m)\\sthe\\smodel\\scontains.*$", "");  // FIXME HACK
				res[0] = res[0].replaceAll("(?m)\\sonly\\sone\\sclaim.*$", "");
				res[0] = res[0].replaceAll("(?m)\\sor\\suse\\se\\.g\\..*$", "");
				res[0] = res[0].replaceAll("(?m)\\schoose\\swhich\\sone.*$", "");
				res[1] = res[1].replace("'gcc-4' is not recognized as an internal or external command,\noperable program or batch file.", "");
				res[1] = res[1].replace("'gcc-3' is not recognized as an internal or external command,\noperable program or batch file.", "");
				res[0] = res[0].trim();
				res[1] = res[1].trim();
				if (!res[0].trim().isEmpty() || !res[1].trim().isEmpty())
				{
					//throw new RuntimeException("[scrib] : " + Arrays.toString(res[0].getBytes()) + "\n" + Arrays.toString(res[1].getBytes()));
					throw new RuntimeException("[-spin] [spin]: " + res[0] + "\n\n" + res[1]);
				}
				int procs = 0;
				for (int i = 0; i < pml.length(); procs++)
				{
					i = pml.indexOf("proctype", i);
					if (i == -1)
					{
						break;
					}
					i++;
				}
				int dnfair = (procs <= 6) ? 2 : 3;  // FIXME
				res = ScribUtil.runProcess("gcc", "-o", "pan", "pan.c", "-DNFAIR=" + dnfair);
				res[0] = res[0].trim();
				res[1] = res[1].trim();
				if (!res[0].isEmpty() || !res[1].isEmpty())
				{
					throw new RuntimeException("[-spin] [gcc]: " + res[0] + "\n\n" + res[1]);
				}
				for (String prop : props)
				{
					if (job.debug)
					{
						System.out.println("[-spin] [pan] Verifying " + prop + ":");
					}
					res = ScribUtil.runProcess("pan", "-a", "-f", "-N", prop);
					res[1] = res[1].replace("warning: no accept labels are defined, so option -a has no effect (ignored)", "");
					res[1] = res[1].replace("warning: only one claim defined, -N ignored", "");
					res[0] = res[0].trim();
					res[1] = res[1].trim();
					if (res[0].contains("error,") || !res[1].isEmpty())
					{
						throw new RuntimeException("[-spin] [pan]: " + res[0] + "\n\n" + res[1]);
					}
					int err = res[0].indexOf("errors: ");
					boolean valid = (res[0].charAt(err + 8) == '0');
					if (!valid)
					{
						System.err.println("[-spin] [pan] " + res[0] + "\n\n" + res[1]);
						return false;
					}
				}
				return true;  // All props valid
			}
			catch (ScribbleException e)
			{
				throw new RuntimeException(e);
			}
			finally
			{
				tmp.delete();
			}
		}
		catch (IOException e)
		{
			throw new RuntimeException(e);
		}
	}

	/*// FIXME: move
	private static boolean runSpin(String prefix, String pml) //throws ScribbleException
	{
		File tmp;
		try
		{
			tmp = File.createTempFile(prefix, ".pml.tmp");
			try
			{
				String tmpName = tmp.getAbsolutePath();				
				ScribUtil.writeToFile(tmpName, pml);
				String[] res = ScribUtil.runProcess("spin", "-a", tmpName);
				res[0] = res[0].replaceAll("(?m)^ltl.*$", "");
				res[1] = res[1].replace("'gcc-4' is not recognized as an internal or external command,\noperable program or batch file.", "");
				res[1] = res[1].replace("'gcc-3' is not recognized as an internal or external command,\noperable program or batch file.", "");
				res[0] = res[0].trim();
				res[1] = res[1].trim();
				if (!res[0].trim().isEmpty() || !res[1].trim().isEmpty())
				{
					//throw new RuntimeException("[scrib] : " + Arrays.toString(res[0].getBytes()) + "\n" + Arrays.toString(res[1].getBytes()));
					throw new RuntimeException("[-spin] [spin]: " + res[0] + "\n" + res[1]);
				}
				int procs = 0;
				for (int i = 0; i < pml.length(); procs++)
				{
					i = pml.indexOf("proctype", i);
					if (i == -1)
					{
						break;
					}
					i++;
				}
				int dnfair = (procs <= 6) ? 2 : 3;  // FIXME
				res = ScribUtil.runProcess("gcc", "-o", "pan", "pan.c", "-DNFAIR=" + dnfair);
				res[0] = res[0].trim();
				res[1] = res[1].trim();
				if (!res[0].isEmpty() || !res[1].isEmpty())
				{
					throw new RuntimeException("[-spin] [gcc]: " + res[0] + "\n" + res[1]);
				}
				res = ScribUtil.runProcess("pan", "-a", "-f");
				res[1] = res[1].replace("warning: no accept labels are defined, so option -a has no effect (ignored)", "");
				res[0] = res[0].trim();
				res[1] = res[1].trim();
				if (res[0].contains("error,") || !res[1].isEmpty())
				{
					throw new RuntimeException("[-spin] [pan]: " + res[0] + "\n" + res[1]);
				}
				int err = res[0].indexOf("errors: ");
				boolean valid = (res[0].charAt(err + 8) == '0');
				if (!valid)
				{
					System.err.println("[-spin] [pan] " + res[0] + "\n" + res[1]);
				}
				return valid;
			}
			catch (ScribbleException e)
			{
				throw new RuntimeException(e);
			}
			finally
			{
				tmp.delete();
			}
		}
		catch (IOException e)
		{
			throw new RuntimeException(e);
		}
	}*/
}

