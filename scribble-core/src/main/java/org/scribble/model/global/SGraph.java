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
package org.scribble.model.global;

import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.scribble.model.MGraph;
import org.scribble.model.global.actions.SAction;
import org.scribble.type.kind.Global;
import org.scribble.type.name.GProtocolName;

public class SGraph extends MGraph<Void, SAction, SState, Global> //implements MPrettyPrint
{
	public final GProtocolName proto;
	//private final Map<Role, EGraph> efsms;
	//private final boolean fair;
	
	/*public final SState init;
	public Map<Integer, SState> states; // State ID -> GMState

	private Map<Integer, Set<Integer>> reach; // State ID -> reachable states (not reflexive)*/
	private Set<Set<Integer>> termSets;

	// Unlike EState, SGraph is not just a "simple wrapper" for an existing graph of nodes -- it is a "semantic structure" that needs to be fully built properly (so no arbitrary "toGraph" method; cf., EState)
	//protected SGraph(GProtocolName proto, Map<Integer, SState> states, SState init)
	protected SGraph(GProtocolName proto, SState init)
	{
		super(init);
		this.proto = proto;
		/*this.init = init;
		this.states = Collections.unmodifiableMap(states);
		this.reach = getReachabilityMap();*/
	}
	
	/*public SModel toModel()
	{
		return new SModel(this);
	}*/

	public Set<Set<Integer>> getTerminalSets()
	{
		if (this.termSets != null)
		{
			return this.termSets;
		}

		Set<Set<Integer>> termSets = new HashSet<>();
		Set<Set<Integer>> checked = new HashSet<>();
		for (Integer i : this.reach.keySet())
		{
			SState s = this.states.get(i);
			Set<Integer> rs = this.reach.get(s.id);
			if (!checked.contains(rs) && rs.contains(s.id))
			{
				checked.add(rs);
				if (isTerminalSetMember(s))
				{
					termSets.add(rs);
				}
			}
		}
		this.termSets = Collections.unmodifiableSet(termSets);
		return this.termSets;
	}

	private boolean isTerminalSetMember(SState s)
	{
		Set<Integer> rs = this.reach.get(s.id);
		Set<Integer> tmp = new HashSet<>(rs);
		tmp.remove(s.id);
		for (Integer r : tmp)
		{
			if (!this.reach.containsKey(r) || !this.reach.get(r).equals(rs))
			{
				return false;
			}
		}
		return true;
	}

	// Pre: reach.get(start).contains(end) // FIXME: will return null if initial
	// state is error
	public List<SAction> getTrace(SState start, SState end)
	{
		return getPath(start, end);
	}


	/*@Override
	public String toDot()
	{
		return this.init.toDot();
	}

	@Override
	public String toAut()
	{
		return this.init.toAut();
	}

	@Override
	public String toString()
	{
		return this.init.toString();
	}*/
}
