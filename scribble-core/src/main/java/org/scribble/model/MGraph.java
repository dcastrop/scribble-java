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
package org.scribble.model;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.SortedMap;
import java.util.TreeMap;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import org.scribble.type.kind.ProtocolKind;

abstract public class MGraph
		<
		L,                             // Node label type (cosmetic)
		A extends MAction<K>,          // Edge type
		S extends MPrettyState<L, A, S, K>,  // State type
		K extends ProtocolKind         // Global/Local
		>
		implements MPrettyPrint
{
	//public final GProtocolName proto;
	
	public Map<Integer, S> states; // State ID -> GMState
	public final S init;
	//public final EState term;  // No -- SGraphs for bad protocols may have multiple terminals

	protected Map<Integer, Set<Integer>> reach; // State ID -> reachable states (not reflexive)
	//private Set<Set<Integer>> termSets;

	// Unlike EState, SGraph is not just a "simple wrapper" for an existing graph of nodes -- it is a "semantic structure" that needs to be fully built properly (so no arbitrary "toGraph" method; cf., EState)
	//protected MGraph(GProtocolName proto, Map<Integer, S> states, S init)
	//protected MGraph(GProtocolName proto, S init)
	protected MGraph(S init)
	{
		//this.proto = proto;
		Set<S> rs = Stream.of(init).collect(Collectors.toSet()); 
		rs.addAll(MState.getReachableStates(init));
		this.states = rs.stream().collect(Collectors.toMap(s -> s.id, s -> s));
		this.init = init;
		this.reach = getReachabilityMap();  // FIXME: optimise: build reachability matrix during underlying graph construction (e.g., SGraphBuilderUtil#buildSGraph)
	}
	
	/*public SModel toModel()
	{
		return new SModel(this);
	}*/

	/*public Set<Set<Integer>> getTerminalSets()
	{
		if (this.termSets != null)
		{
			return this.termSets;
		}

		Set<Set<Integer>> termSets = new HashSet<>();
		Set<Set<Integer>> checked = new HashSet<>();
		for (Integer i : reach.keySet())
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
		SortedMap<Integer, Set<Integer>> candidates = new TreeMap<>();
		Set<Integer> dis0 = new HashSet<Integer>();
		dis0.add(start.id);
		candidates.put(0, dis0);

		Set<Integer> seen = new HashSet<>();
		seen.add(start.id);

		return getTraceAux(new LinkedList<>(), seen, candidates, end);
	}

	// Djikstra's
	private List<SAction> getTraceAux(List<SAction> trace, Set<Integer> seen,
			SortedMap<Integer, Set<Integer>> candidates, SState end)
	{
		Integer dis = candidates.keySet().iterator().next();
		Set<Integer> cs = candidates.get(dis);
		Iterator<Integer> it = cs.iterator();
		Integer currid = it.next();
		it.remove();
		if (cs.isEmpty())
		{
			candidates.remove(dis);
		}

		SState curr = this.states.get(currid);
		Iterator<SAction> as = curr.getAllActions().iterator();
		Iterator<SState> ss = curr.getAllSuccessors().iterator();
		while (as.hasNext())
		{
			SAction a = as.next();
			SState s = ss.next();
			if (s.id == end.id)
			{
				trace.add(a);
				return trace;
			}

			if (!seen.contains(s.id) && this.reach.containsKey(s.id)
					&& this.reach.get(s.id).contains(end.id))
			{
				seen.add(s.id);
				Set<Integer> tmp1 = candidates.get(dis + 1);
				if (tmp1 == null)
				{
					tmp1 = new HashSet<>();
					candidates.put(dis + 1, tmp1);
				}
				tmp1.add(s.id);
				List<SAction> tmp2 = new LinkedList<>(trace);
				tmp2.add(a);
				List<SAction> res = getTraceAux(tmp2, seen, candidates, end);
				if (res != null)
				{
					return res;
				}
			}
		}
		return null;
	}*/

	// Not reflexive
	protected Map<Integer, Set<Integer>> getReachabilityMap()
	{
		if (this.reach != null)  // Now redundant, set by constructor
		{
			return this.reach;
		}

		Map<Integer, Integer> idToIndex = new HashMap<>(); // state ID -> array index
		Map<Integer, Integer> indexToId = new HashMap<>(); // array index -> state ID
		int i = 0;
		for (S s : this.states.values())
		{
			idToIndex.put(s.id, i);
			indexToId.put(i, s.id);
			i++;
		}
		this.reach = getReachabilityAux(idToIndex, indexToId);

		return this.reach;
	}

	private Map<Integer, Set<Integer>> getReachabilityAux(
			Map<Integer, Integer> idToIndex, Map<Integer, Integer> indexToId)
	{
		int size = idToIndex.keySet().size();
		boolean[][] reach = new boolean[size][size];

		for (Integer s1id : idToIndex.keySet())
		{
			for (S s2 : this.states.get(s1id).getAllSuccessors())
			{
				reach[idToIndex.get(s1id)][idToIndex.get(s2.id)] = true;
			}
		}

		for (boolean again = true; again;)
		{
			again = false;
			for (int i = 0; i < size; i++)
			{
				for (int j = 0; j < size; j++)
				{
					if (reach[i][j])
					{
						for (int k = 0; k < size; k++)
						{
							if (reach[j][k] && !reach[i][k])
							{
								reach[i][k] = true;
								again = true;
							}
						}
					}
				}
			}
		}

		Map<Integer, Set<Integer>> res = new HashMap<>();
		for (int i = 0; i < size; i++)
		{
			Set<Integer> tmp = res.get(indexToId.get(i));
			for (int j = 0; j < size; j++)
			{
				if (reach[i][j])
				{
					if (tmp == null)
					{
						tmp = new HashSet<>();
						res.put(indexToId.get(i), tmp);
					}
					tmp.add(indexToId.get(j));
				}
			}
		}

		return Collections.unmodifiableMap(res);
	}
	
	// Must work for start.id == end.id (i.e., cycles, not "empty path")
	public List<List<A>> getAllPaths(S start, S end)
	{
		List<List<A>> res = new LinkedList<>();
		for (A a : start.getAllActions())
		{
			S succ = start.getSuccessor(a);
			if (succ.id == end.id)
			{
				res.add(Stream.of(a).collect(Collectors.toList()));
			}
			else if (this.reach.get(succ).contains(end))
			{
				for (List<A> p : getAllPaths(succ, end))
				{
					p.add(0, a);
					res.add(p);
				}
			}
		}
		return res;
	}

	public List<A> getPath(S start, S end)
	{
		SortedMap<Integer, Set<Integer>> candidates = new TreeMap<>();
		Set<Integer> dis0 = new HashSet<Integer>();
		dis0.add(start.id);
		candidates.put(0, dis0);

		Set<Integer> seen = new HashSet<>();
		seen.add(start.id);

		return getPath(new LinkedList<>(), seen, candidates, end);
	}

	// Djikstra's
	private List<A> getPath(List<A> trace, Set<Integer> seen,
			SortedMap<Integer, Set<Integer>> candidates, S end)
	{
		Integer dis = candidates.keySet().iterator().next();
		Set<Integer> cs = candidates.get(dis);
		Iterator<Integer> it = cs.iterator();
		Integer currid = it.next();
		it.remove();
		if (cs.isEmpty())
		{
			candidates.remove(dis);
		}

		S curr = this.states.get(currid);
		Iterator<A> as = curr.getAllActions().iterator();
		Iterator<S> ss = curr.getAllSuccessors().iterator();
		while (as.hasNext())
		{
			A a = as.next();
			S s = ss.next();
			if (s.id == end.id)
			{
				trace.add(a);
				return trace;
			}

			if (!seen.contains(s.id) && this.reach.containsKey(s.id)
					&& this.reach.get(s.id).contains(end.id))
			{
				seen.add(s.id);
				Set<Integer> tmp1 = candidates.get(dis + 1);
				if (tmp1 == null)
				{
					tmp1 = new HashSet<>();
					candidates.put(dis + 1, tmp1);
				}
				tmp1.add(s.id);
				List<A> tmp2 = new LinkedList<>(trace);
				tmp2.add(a);
				List<A> res = getPath(tmp2, seen, candidates, end);
				if (res != null)
				{
					return res;
				}
			}
		}
		return null;
	}

	/*// Not reflexive
	public Map<Integer, Set<Integer>> getReachabilityMap()
	{
		if (this.reach != null)
		{
			return this.reach;
		}

		Map<Integer, Integer> idToIndex = new HashMap<>(); // state ID -> array index
		Map<Integer, Integer> indexToId = new HashMap<>(); // array index -> state ID
		int i = 0;
		for (SState s : this.states.values())
		{
			idToIndex.put(s.id, i);
			indexToId.put(i, s.id);
			i++;
		}
		this.reach = getReachabilityAux(idToIndex, indexToId);

		return this.reach;
	}

	private Map<Integer, Set<Integer>> getReachabilityAux(
			Map<Integer, Integer> idToIndex, Map<Integer, Integer> indexToId)
	{
		int size = idToIndex.keySet().size();
		boolean[][] reach = new boolean[size][size];

		for (Integer s1id : idToIndex.keySet())
		{
			for (SState s2 : this.states.get(s1id).getAllSuccessors())
			{
				reach[idToIndex.get(s1id)][idToIndex.get(s2.id)] = true;
			}
		}

		for (boolean again = true; again;)
		{
			again = false;
			for (int i = 0; i < size; i++)
			{
				for (int j = 0; j < size; j++)
				{
					if (reach[i][j])
					{
						for (int k = 0; k < size; k++)
						{
							if (reach[j][k] && !reach[i][k])
							{
								reach[i][k] = true;
								again = true;
							}
						}
					}
				}
			}
		}

		Map<Integer, Set<Integer>> res = new HashMap<>();
		for (int i = 0; i < size; i++)
		{
			Set<Integer> tmp = res.get(indexToId.get(i));
			for (int j = 0; j < size; j++)
			{
				if (reach[i][j])
				{
					if (tmp == null)
					{
						tmp = new HashSet<>();
						res.put(indexToId.get(i), tmp);
					}
					tmp.add(indexToId.get(j));
				}
			}
		}

		return Collections.unmodifiableMap(res);
	}*/

	@Override
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
	}
}
