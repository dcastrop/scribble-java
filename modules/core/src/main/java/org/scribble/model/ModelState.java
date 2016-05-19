package org.scribble.model;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.Map.Entry;
import java.util.Set;

import org.scribble.sesstype.kind.ProtocolKind;
import org.scribble.sesstype.name.RecVar;

//public class ModelState<K extends ProtocolKind>
public class ModelState<A extends ModelAction<K>, S extends ModelState<A, S, K>, K extends ProtocolKind>
{
	private static int count = 0;  // FIXME: factor out with ModelAction
	
	public final int id;

	protected final Set<RecVar> labs;  // Was RecVar and SubprotocolSigs, now using inlined protocol for FSM building so just RecVar
	//private final Set<String> labs;  // Something better to cover both RecVar and SubprotocolSigs?
	protected final LinkedHashMap<A, S> edges;  // Want predictable ordering of entries for e.g. API generation (state enumeration)*/
	
	public ModelState(Set<RecVar> labs)  // Immutable singleton node
	//public GModelState(Set<String> labs)  // Immutable singleton node
	//public GModelState()  // Immutable singleton node
	{
		this.id = ModelState.count++;
		this.labs = new HashSet<>(labs);
		this.edges = new LinkedHashMap<>();
	}
	
	protected void addLabel(RecVar lab)
	{
		this.labs.add(lab);
	}
	
	// Mutable (can also overwrite edges)
	protected void addEdge(A a, S s)
	{
		this.edges.put(a, s);
	}
	
	public Set<RecVar> getLabels()
	{
		return Collections.unmodifiableSet(this.labs);
	}
	
	public Set<A> getAcceptable()
	{
		return Collections.unmodifiableSet(this.edges.keySet());
	}
	
	public boolean isAcceptable(A a)
	{
		return this.edges.containsKey(a);
	}

	public S accept(A a)
	{
		return this.edges.get(a);
	}
	
	public Collection<S> getSuccessors()
	{
		return Collections.unmodifiableCollection(this.edges.values());
	}
	
	public boolean isTerminal()
	{
		return this.edges.isEmpty();
	}

	@Override
	public final int hashCode()
	{
		int hash = 73;
		hash = 31 * hash + this.id;
		return hash;
	}

	@Override
	public boolean equals(Object o)
	{
		if (this == o)
		{
			return true;
		}
		if (!(o instanceof ModelState))
		{
			return false;
		}
		return this.id == ((ModelState<?, ?, ?>) o).id;
	}
	
	@Override
	public String toString()
	{
		/*String s = "\"" + this.id + "\":[";
		if (!this.edges.isEmpty())
		{
			Iterator<Entry<A, S>> es = this.edges.entrySet().iterator();
			Entry<A, S> first = es.next();
			s += first.getKey() + "=\"" + first.getValue().id + "\"";
			while (es.hasNext())
			{
				Entry<A, S> e = es.next();
				s += ", " + e.getKey() + "=\"" + e.getValue().id + "\"";
			}
		}
		return s + "]";*/
		return Integer.toString(this.id);  // FIXME
	}
	
	public final String toDot()
	{
		String s = "digraph G {\n" // rankdir=LR;\n
				+ "compound = true;\n";
		s += toDot(new HashSet<>());
		return s + "\n}";
	}

	//protected final String toDot(Set<S> seen)
	protected final String toDot(Set<ModelState<A, S, K>> seen)
	{
		seen.add(this);
		String s = toNodeDot();
		for (Entry<A, S> e : this.edges.entrySet())
		{
			A msg = e.getKey();
			S p = e.getValue();
			s += "\n" + toEdgeDot(msg, p);
			if (!seen.contains(p))
			{
				s += "\n" + p.toDot(seen);
			}
		}
		return s;
	}

	protected final String toEdgeDot(String src, String dest, String lab)
	{
		return src + " -> " + dest + " [ " + lab + " ];";
	}

	// dot node declaration
	// Override to change drawing declaration of "this" node
	protected String toNodeDot()
	{
		return getDotNodeId() + " [ " + getNodeLabel() + " ];";
	}
	
	protected String getNodeLabel()
	{
		String labs = this.labs.toString();
		//return "label=\"" + labs.substring(1, labs.length() - 1) + "\"";
		return "label=\"" + this.id + ": " + labs.substring(1, labs.length() - 1) + "\"";  // FIXME
	}
	
	protected String getDotNodeId()
	{
		return "\"" + this.id + "\"";
	}

	// Override to change edge drawing from "this" as src
	protected String toEdgeDot(A msg, S next)
	{
		return toEdgeDot(getDotNodeId(), next.getDotNodeId(), next.getEdgeLabel(msg));
	}
	
	// "this" is the dest node of the edge
	// Override to change edge drawing to "this" as dest
	protected String getEdgeLabel(A msg)
	{
		return "label=\"" + msg + "\"";
	}

	public static <A extends ModelAction<K>, S extends ModelState<A, S, K>, K extends ProtocolKind>
			S findTerminalState(Set<S> visited, S curr)
	{
		if (!visited.contains(curr))
		{
			if (curr.isTerminal())
			{
				return curr;
			}
			visited.add(curr);
			for (S succ : curr.getSuccessors())
			{
				S res = findTerminalState(visited, succ);
				if (res != null)
				{
					return res;
				}
			}
		}
		return null;
	}
	
	
	/*protected Map<ModelAction, ModelState> getEdges()
	{
		return this.edges;
	}* /

	protected void addLabel(RecVar lab)
	{
		this.labs.add(lab);
	}
	
	public void addEdge(GModelAction a, GModelState s)
	{
		this.edges.put(a, s);
	}
	
	public Set<RecVar> getLabels()
	//public Set<String> getLabels()
	{
		return new HashSet<>(this.labs);
	}
	
	public Set<GModelAction> getAcceptable()
	{
		return new HashSet<>(this.edges.keySet());
	}
	
	public boolean isAcceptable(GModelAction a)
	{
		return this.edges.containsKey(a);
	}

	public GModelState accept(GModelAction a)
	{
		return this.edges.get(a);
	}
	
	public Collection<GModelState> getSuccessors()
	{
		return this.edges.values();
	}
	
	public boolean isTerminal()
	{
		return this.edges.isEmpty();
	}
	
	public Set<GModelState> findTerminals()
	{
		Set<GModelState> terms = new HashSet<>();
		findTerminals(new HashSet<>(), this, terms);
		return terms;
	}

	private static void findTerminals(Set<GModelState> seen, GModelState curr, Set<GModelState> terms)
	{
		if (seen.contains(curr))
		{
			return;
		}
		seen.add(curr);
		if (curr.isTerminal())
		{
			terms.add(curr);
		}
		else
		{
			for (Entry<GModelAction, GModelState> e : curr.edges.entrySet())
			{
				findTerminals(seen, e.getValue(), terms);
			}
		}
	}

	@Override
	public int hashCode()
	{
		int hash = 73;
		hash = 31 * hash + this.id;  // Would be enough by itself, but keep consistent with equals
		/*hash = 31 * hash + this.labs.hashCode();
		hash = 31 * hash + this.edges.hashCode();* /
		return hash;
	}

	@Override
	public boolean equals(Object o)
	{
		if (this == o)
		{
			return true;
		}
		if (!(o instanceof GModelState))
		{
			return false;
		}
		GModelState s = (GModelState) o;
		return this.id == s.id;// && this.labs.equals(s.labs) && this.edges.equals(s.edges);
	}
	
	@Override
	public String toString()
	{
		String s = "\"" + this.id + "\":[";
		if (!this.edges.isEmpty())
		{
			Iterator<Entry<GModelAction, GModelState>> es = this.edges.entrySet().iterator();
			Entry<GModelAction, GModelState> first = es.next();
			s += first.getKey() + "=\"" + first.getValue().id + "\"";
			while (es.hasNext())
			{
				Entry<GModelAction, GModelState> e = es.next();
				s += ", " + e.getKey() + "=\"" + e.getValue().id + "\"";
			}
		}
		return s + "]";
	}
	
	public final String toDot()
	{
		String s = "digraph G {\n" // rankdir=LR;\n
				+ "compound = true;\n";
		s += toDot(new HashSet<>());
		return s + "\n}";
	}

	protected final String toDot(Set<GModelState> seen)
	{
		seen.add(this);
		String s = toNodeDot();
		for (Entry<GModelAction, GModelState> e : this.edges.entrySet())
		{
			GModelAction msg = e.getKey();
			GModelState p = e.getValue();
			s += "\n" + toEdgeDot(msg, p);
			if (!seen.contains(p))
			{
				s += "\n" + p.toDot(seen);
			}
		}
		return s;
	}

	protected final String toEdgeDot(String src, String dest, String lab)
	{
		return src + " -> " + dest + " [ " + lab + " ];";
	}

	// dot node declaration
	// Override to change drawing declaration of "this" node
	protected String toNodeDot()
	{
		return getDotNodeId() + " [ " + getNodeLabel() + " ];";
	}
	
	protected String getNodeLabel()
	{
		/*String labs = this.labs.toString();
		return "label=\"" + labs.substring(1, labs.length() - 1) + "\"";* /
		return "";
	}
	
	protected String getDotNodeId()
	{
		return "\"" + this.id + "\"";
	}

	// Override to change edge drawing from "this" as src
	protected String toEdgeDot(GModelAction msg, GModelState next)
	{
		return toEdgeDot(getDotNodeId(), next.getDotNodeId(), next.getEdgeLabel(msg));
	}
	
	// "this" is the dest node of the edge
	// Override to change edge drawing to "this" as dest
	protected String getEdgeLabel(GModelAction msg)
	{
		return "label=\"" + msg + "\"";
	}
	
	/*public ModelState copy()
	{
		ModelState copy = new ModelState(this.labs);
		copy(new HashSet<>(), this, copy);
		return copy;
	}

	public static void copy(Set<ModelState> seen, ModelState curr, ModelState copy)
	{
		if (seen.contains(curr))
		{
			return;
		}
		seen.add(curr);
		for(Entry<Op, ModelState> e : curr.edges.entrySet())
		{
			Op op = e.getKey();
			ModelState next = e.getValue();
			ModelState tmp = new ModelState(next.labs);
			copy.edges.put(op, tmp);
			copy(seen, next, tmp);
		}
	}*/
}