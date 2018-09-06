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
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
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
import org.scribble.model.endpoint.actions.EAction;
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
			pml += "chan sync_" + p[0] + "_" + p[1] + " = [0] of { mtype };\n"
					
					+ "chan s_" + p[0] + "_" + p[1] + " = [1] of { mtype };\n"  // FIXME: rename "s" prefix
								// Async queue size 1 even though separate s/r chans, to work with guarded inputs
								// But this interferes with 1-bounded (2-bounded?), and eventual stability?
					 //+ "chan r_" + p[0] + "_" + p[1] + " = [1] of { mtype };\n"

					 //+ "bool empty_" + p[0] + "_" + p[1] + " = true;\n"
					+ "int status_" + p[0] + "_" + p[1] + " = "
							+ (gpd.isExplicitModifier() ? "-1" : "0") + ";\n"  // -1 = disconnected, 0 = empty, 1 = non-empty

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
		}

		// FIXME split termination-fairness and non-terminating-fairness
		boolean termFair = gs.values().stream().allMatch(g -> g.isTermFair());  // FIXME: only needed if -fair
		Map<Integer, Map<Integer, List<EAction>>> fairAndNonTermFairActions = new HashMap<>();   // FIXME: categorise all recursions as term-fair and non-term-fair, and gen fair clauses accordingly
				// For all endpoints, state id's globally unique
				// Empty means non-fair, or term-fair, or no poly output choice paths to treat
				// "Distinguishing" action may be an input, e.g., rec X { A->B.X + A->B.(B->A.X + B->A.X) } -- "duplicate" treatment at A's and B's output choices (necessary)  
						// FIXME: work out "recursion decision actions" properly, e.g., rec X { A->B . (B->A.X + B->A.X) }, "decision state" is only at B (not also A, unlike above) -- N.B. a rec may have multiple different decision roles (e.g., above example, both A and B)
		Map<Integer, List<EAction>> fairAndNonTermFairActions2 = new HashMap<>();   
				// Above has output choice state as key; here is the "actual" action state (may be different)
				// FIXME #2 is now redundant (info is in #1)

		//System.out.println("1111: " + termFair);
		
		for (Role r : rs)
		{
			EGraph g = gs.get(r);

			if (fair && !termFair)
			{
				Set<EState> reach = Stream.of(g.init).collect(Collectors.toSet());
				reach.addAll(MState.getReachableStates(g.init));
				
				
				// FIXME:  filter all recursion entrys, and categorise term or term-set
				
				
				Set<EState> filtered = reach.stream().filter(s -> !s.getLabels().isEmpty() && s.getStateKind() == EStateKind.OUTPUT
						&& s.isTermSetEntry()).collect(Collectors.toSet());  // Includes #succs == 1, e.g., rec X { a1 . ( a2.X + a3.X ) }
				for (EState s : filtered)
				{
					List<List<EAction>> ps = g.getAllPaths(s, s);  // CHECKME: non-deterministic paths? -- N.B. mostly using -minlts with -spin
					
					//System.out.println("AAAA: " + ps);
					
					Function<List<EAction>, EAction> f = p ->
							p.stream().filter(a -> ps.stream().filter(pp -> !p.equals(pp)).allMatch(pp -> !pp.contains(a))).findFirst().get();
					if (ps.size() > 1)
					{
						Map<Integer, List<EAction>> tmp0 = new HashMap<>();
						fairAndNonTermFairActions.put(s.id, tmp0);
						pml += "\n";
						for (List<EAction> p : ps)
						{
							EAction a = f.apply(p);
							//tmp.add(a);
							EState ss = g(s, p, a);
							List<EAction> tmp2 = fairAndNonTermFairActions2.get(ss.id);
							if (tmp2 == null)
							{
								tmp2 = new LinkedList<>();
								fairAndNonTermFairActions2.put(ss.id, tmp2);
							}
							tmp2.add(a);
							List<EAction> tmp = tmp0.get(ss.id);
							if (tmp == null)
							{
								tmp = new LinkedList<>();
								tmp0.put(ss.id, tmp);
							}
							tmp.add(a);
							pml += "\nbool " + r + ss.id + "_" + a.mid + " = false;";  // FIXME: factor out label (EState#toPml)
						}
					}
				}
			}

			//System.out.println("BBBB: " + fairAndNonTermFairActions);
			
			pml += "\n\n" + g.toPml(r, fairAndNonTermFairActions2);  // FIXME
		}
		if (job.debug)
		{
			System.out.println("[-spin]: Promela processes\n" + pml + "\n");
		}

		if (fair)
		{
			if (termFair)
			{
				validateBySpinTermFair(job, fullname, gpd, rs, pairs, pml, true);  // FIXME: also use this if no recursions, if faster (since -fair irrelevant)
			}
			else
			{
				validateBySpinNonTermFair(job, fullname, gpd, rs, pairs, pml, true, fairAndNonTermFairActions);
			}
		}
		else
		{
			validateBySpinNonTermFair(job, fullname, gpd, rs, pairs, pml, false, Collections.emptyMap());
		}
	}
	
	private static EState g(EState s, List<EAction> p, EAction a)
	{
		for (EAction aa : p)
		{
			if (aa.equals(a))  // Must be first "a" in "p" (cf. findFirst); otherwise "a" would be in some other path
			{
				return s;
			}
			s = s.getSuccessor(aa);
		}
		throw new RuntimeException("Shouldn't get in here: " + s + ", " + p + ", " + a);
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

			String curr = null;
			if (g.term != null)
			{
				//clauses.add(r + "@" + getPmlLabel(r, g.term));
				curr = r + "@" + getPmlLabel(r, g.term);
				tmp.remove(g.term);
			}
			for (EState s : tmp)  // Throws exception, cannot use flatMap
			{
				EStateKind kind = s.getStateKind();
				if (kind == EStateKind.UNARY_INPUT || kind == EStateKind.POLY_INPUT)  // FIXME: include outputs due to bounded model?  or subsumed by eventual stability
				{
					//clauses.add("!<>[]" + r + "@" + getPmlLabel(r, s));  // FIXME: factor out label  // Now done in via term states (above)
				}
				else if (kind == EStateKind.ACCEPT)  // FIXME: some "accept states" should not be accepting, e.g., A->>B.A->B -- but any error would come out in the wash at some other role?
				{
					if (curr == null)
					{
						curr = "";
					}
					else
					{
						curr += " || ";
					}
					curr += r + "@" + getPmlLabel(r, s);
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
			}

			clauses.add("(" + curr + ")");
		}
		String eventualStability = "";
		for (Role[] p : pairs)
		{
			eventualStability += (((eventualStability.isEmpty()) ? "" : " && ")
					//+ "empty_" + p[0] + "_" + p[1]);  // "eventual reception", not eventual stability
					+ "(status_" + p[0] + "_" + p[1] + " <= 0)");  // "eventual reception", not eventual stability
							// FIXME: tie 0 case more specifically to end state; and -1 case may be end or accepting states

					// FIXME: eventual stability too strong -- can be violated by certain interleavings keeping alternate queues non-empty
					// N.B. "fairness" fixes the above for recursions-with-exits, since exit always eventually taken (so, eventual stable termination)
		}
		clauses.add(eventualStability);

		Map<String, String> props = new HashMap<>();
		int batchSize = 999999;  // FIXME: remove batching, redundant here
		if (!fair)  // Currently redundant (and incorrect, for term-fair)
		{
			for (int i = 0, k = 1; i < clauses.size(); k++)
			{
				int j = (i+batchSize < clauses.size()) ? i+batchSize : clauses.size();
				String batch = "<>"//[]  // CHEKME: <>[]p holds for all p (including false) if process stuck?  (<>[]p && !<>[]p && <>[]!p && ...)
						+ "(" + clauses.subList(i, j).stream().collect(Collectors.joining(" && ")) + ")";
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
		}
		else
		{
			// Default spin check checks term reachable (i.e., "fair choices"?) and safe
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
			List<Role> rs, List<Role[]> pairs, String pml, boolean fair, Map<Integer, Map<Integer, List<EAction>>> fairAndNonTermFairActions) throws ScribbleException
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
			for (EState s : tmp)  // Throws exception, cannot use flatMap
			{
				EStateKind kind = s.getStateKind();
				if (kind == EStateKind.UNARY_INPUT || kind == EStateKind.POLY_INPUT)  // FIXME: include outputs due to bounded model?  or subsumed by eventual stability
				{
					clauses.add("<>!" + r + "@" + getPmlLabel(r, s));  // [] will be added to whole batch  // FIXME: factor out label
							// FIXME: refine clause by whether state is fair+end-reachable, or otherwise (e.g., term set)?
				}
				else if (kind != EStateKind.OUTPUT && kind != EStateKind.TERMINAL && kind != EStateKind.ACCEPT)  // All "accept states" allowed to be accepting
				{
					throw new RuntimeException("[-spin] TODO: " + kind);
				}
				// N.B. fairAndNonTermFairActions action may not be directly from "s" ("offset" recursions)
				if (fairAndNonTermFairActions.containsKey(s.id))  // !fairAndNonTermFairActions.isEmpty() implies fair and non term-fair
				{
					String fc = "([]<>" + r + "@" + getPmlLabel(r, s) + " -> []<>(";
					//fc += fairAndNonTermFairActions.get(s.id).stream().map(a -> "<>" + r + s.id + "_" + a.mid).collect(Collectors.joining(" && "));  // FIXME: factor out label
					fc += fairAndNonTermFairActions.get(s.id).entrySet().stream()
							//.map(a -> r.toString() + s.id + "_" + a.mid).collect(Collectors.joining(" && "));  // FIXME: factor out label
							.flatMap(e -> e.getValue().stream().map(a -> r.toString() + e.getKey() + "_" + a.mid))
							.collect(Collectors.joining(" && "));  // FIXME: factor out label
					fc += "))";
					fairChoices.add(fc);
							// Alternative would be to implement a "scheduler" for (infinitely occurring) output choices and show it's sound to use
				}
			}
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
			//String eventualReception = "<>empty_" + p[0] + "_" + p[1];  // [] will be added to whole batch
			String eventualReception = "<>(status_" + p[0] + "_" + p[1] + " <= 0)";  // [] will be added to whole batch

			clauses.add(eventualReception);
					// N.B. "LTL eventual-reception" not technically comparable to "CTL eventual-stability"?  but OK for MPST safety/prog
					// CHECKME: model could be restricted to support eventual stability with extra conditions, e.g., "eager" eating? -- cf. compat side conditions
		}
		/*eventualStability = "[](" + eventualStability + ")";
		//eventualStability = "[]<>(" + eventualStability + ")";
		clauses.add(eventualStability);*/

		Map<String, String> props = new LinkedHashMap<>();
		//int batchSize = 10;  // FIXME: factor out
		int batchSize = 1;  // FIXME: factor out  
				// FIXME: dynamic batch sizing based on previous batch duration?  
				// CHECKME: batching better for error reporting?  (batchSize=1 best?) -- and parallelisation
				// FIXME: batching should be rewritten, e.g., from [](<>!B@labelB13 && <>(!!)empty_C_B) to !<>[](B@labelB13 || !empty_C_B) ?
		for (int i = 0, k = 1; i < clauses.size(); k++)
		{
			int j = (i+batchSize < clauses.size()) ? i+batchSize : clauses.size();
			String batch = "[](" + clauses.subList(i, j).stream().collect(Collectors.joining(" && ")) + ")";
			String ltl =
					  "ltl p" + k + " {\n"
					+ ((fair && !fairChoices.isEmpty()) ? "(" + fairChoices.stream().map(c -> c.toString()).collect(Collectors.joining(" && ")) + ")\n->\n" : "")  // FIXME: filter by batching? -- optimise batches more "semantically"?
					+ "(" + batch + ")"
					+ "\n" + "}";
			
						// FIXME 1: do term-fair or non-term-fair on a per-recursion basis, e.g., term and term set both possible
								// but need to consider, e.g., term-recursion nested within a term set -- primitive option: don't do <>[]!s (never come back), do [](s -> <>(exit1 || exit2 || ...)) ?  
								// but above doesn't repeat exits fairly if nested in term set? -- if within term-set, should just skip
						// FIXME 2: derive "necessary" fair clauses for each property from G ?  e.g., to separate mutually exclusive term sets
								// and group properties with same necesary fair clauses?
						// FIXME 3: combine fair clauses where applicable (within term sets? -- for different roles?), e.g. (a -> b) && (c -> d) => (a && b) -> (c && d)

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
				res = ScribUtil.runProcess("gcc", "-o", "pan", "pan.c", "-DNFAIR=" + dnfair, "-DNOREDUCE");
						// FIXME: -DNOREDUCE "p.o. reduction not compatible with fairness (-f) in models with rendezvous operations" -- change connection establishment to async-ack
				res[0] = res[0].trim();
				res[1] = res[1].trim();
				if (!res[0].isEmpty() || !res[1].isEmpty())
				{
					throw new RuntimeException("[-spin] [gcc]: " + res[0] + "\n\n" + res[1]);
				}
				if (props.isEmpty())
				{
						if (job.debug)
						{
							System.out.println("[-spin] [pan] Verifying -a -f -q:");
						}
						res = ScribUtil.runProcess("pan", "-a", "-f", "-q");
						return checkSpinResult(res);
				}
				else
				{
					for (String prop : props)
					{
						if (job.debug)
						{
							System.out.println("[-spin] [pan] Verifying -a -f -N " + prop + ":");
						}
						res = ScribUtil.runProcess("pan", "-a", "-f", "-N", prop);
						if (!checkSpinResult(res))
						{
							return false;
						}
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

	private static boolean checkSpinResult(String[] res)
	{
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
		return true;
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

