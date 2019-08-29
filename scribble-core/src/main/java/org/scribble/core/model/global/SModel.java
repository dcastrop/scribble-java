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
package org.scribble.core.model.global;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;
import java.util.SortedMap;
import java.util.TreeMap;
import java.util.stream.Collectors;

import org.scribble.core.job.Core;
import org.scribble.core.model.endpoint.actions.ESend;
import org.scribble.core.type.name.Role;
import org.scribble.util.ScribException;


// For doing validation operations on an SGraph (cf. EFsm, use Graph as an FSM)
public class SModel
{
	//private Core core;  // CHECKME: refactor?  but avoiding in constructor to keep mf more independent/uniform

	public final SGraph graph;

	protected SModel(SGraph graph)
	{
		this.graph = graph;
	}

	// CHECKME: let Core call check safety/progress directly? (to avoid passing core -- only used for NO_PROGRESS)
	public void validate(Core core) throws ScribException
	{
		//this.core = core;

		SortedMap<Integer, ? extends SStateErrors> sErrs = getSafetyErrors();
		SProgressErrors pErrs = null;
		if (!core.config.args.NO_PROGRESS)
		{
			 pErrs = new SProgressErrors(this);
		}

		String msg = "";
		if (!sErrs.isEmpty())
		{
			msg += sErrs.values().stream()
					.map(x -> x.toErrorMessage(this.graph))
					.collect(Collectors.joining(""));
		}
		if (!core.config.args.NO_PROGRESS && !pErrs.isEmpty())
		{
			msg += pErrs.toErrorMessage();
		}
		if (!msg.equals(""))
		{
			throw new ScribException(this.graph.proto + ": " + msg);
		}
	}

	protected SortedMap<Integer, ? extends SStateErrors> getSafetyErrors()  // s.id key lighter than full SConfig
	{
		SortedMap<Integer, SStateErrors> res = new TreeMap<>();
		for (int id : this.graph.states.keySet())
		{
			SStateErrors errs = this.graph.states.get(id).getErrors();
			if (!errs.isEmpty())
			{
				res.put(id, errs);
			}
		}
		return res;
	}

	// Progress errs are checked only on termsets (cf. safety checked on all), and "overlap" with safety errors within there
	// Could "skip" safety checks for termsets (probably better than coercing "progress" outside of termsets, as it would probably just amount to safety anyway)
	// CHECKME: factor out a TermSet class?

	protected Map<Set<SState>, Set<Role>> getRoleProgErrors()
	{
		Map<Set<SState>, Set<Role>> res = new HashMap<>();
		Set<Set<SState>> termsets = this.graph.getTermSets();
		for (Set<SState> ts : termsets)
		{
			Set<Role> err = checkRoleProgress(ts);
			if (!err.isEmpty())
			{
				res.put(ts, err);
			}
		}
		return res;
	}

	// Could subsume terminal state check, if terminal sets included size 1 with reflexive reachability (but not a good approach)
	protected Set<Role> checkRoleProgress(Set<SState> termset)
	{
		SState s = termset.iterator().next();  // Pick any state to check canSafelyTerminate (later, if needed), if non progressing equivalent for all
		Set<Role> todo = new HashSet<>(s.config.efsms.keySet());
		for (Iterator<SState> i = termset.iterator(); 
				i.hasNext() && !todo.isEmpty(); )
		{
			i.next().getActions().stream().map(x -> x.subj).distinct()
					.forEachOrdered(x -> todo.remove(x));
				// cf. a.containsRole(r) -- implies obj will be subj for the counterpart action somewhere in the termset?
		}

		// todo is now all roles that are not the subj of any action in the termset
		return todo.stream()
				.filter(x -> !s.config.canSafelyTerminate(x)
						&& s.config.queues.getQueue(x).values().stream()
								.allMatch(y -> y == null))  // Check empty queues for starved -- o/w, is a stuck-message
				.collect(Collectors.toSet());
	}

	protected Map<Set<SState>, Map<Role, Set<ESend>>> getEventualRecepErrors()
	{
		Map<Set<SState>, Map<Role, Set<ESend>>> res = new HashMap<>();
		Set<Set<SState>> termsets = this.graph.getTermSets();
		for (Set<SState> ts : termsets)
		{
			Map<Role, Set<ESend>> err = checkEventualReception(ts);
			if (!err.isEmpty())
			{
				res.put(ts, err);
			}
		}
		return res;
	}

	// cf. eventual stability (could also check within termsets)
	protected Map<Role, Set<ESend>> checkEventualReception(Set<SState> termset)
	{
		SState s0 = termset.iterator().next();
		Set<Role> roles = s0.config.efsms.keySet();
		Map<Role, Map<Role, ESend>> q0 = s0.config.queues.getQueues();  // dest -> src -> msg -- dest.equals(msg.peer), msg is ESend to the dst
		for (Role r1 : roles)
		{
			Map<Role, ESend> q0_r1 = q0.get(r1);
			for (Role r2 : roles)
			{
				if (!r1.equals(r2) && q0_r1.get(r2) != null &&
						termset.stream()
								.anyMatch(x -> x.config.queues.getQueue(r1).get(r2) == null))
				{
					q0_r1.put(r2, null);
				}
			}
		}
	
		// q0 now shows which buffers are never null at any state in the termset
		Map<Role, Set<ESend>> ignored = new HashMap<>();
		for (Role r : roles)
		{
			Set<ESend> msgs = q0.values().stream()
					.flatMap(x -> x.entrySet().stream())  // For all input buffs at every role...
					.filter(x -> x.getKey().equals(r) && x.getValue() != null)  // ...s.t. the buff is from "r" and is non-empty
					.map(x -> x.getValue()).collect(Collectors.toSet());
			if (!msgs.isEmpty())
			{
				ignored.put(r, msgs);
			}
		}
		return ignored;
	}
}
