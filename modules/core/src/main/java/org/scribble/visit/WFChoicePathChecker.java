package org.scribble.visit;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.scribble.ast.Module;
import org.scribble.ast.ProtocolDecl;
import org.scribble.ast.ScribNode;
import org.scribble.ast.global.GProtocolDecl;
import org.scribble.main.ScribbleException;
import org.scribble.model.global.GModel;
import org.scribble.model.global.GModelAction;
import org.scribble.model.global.GModelPath;
import org.scribble.model.global.GModelState;

// Duplicated from WFChoiceChecker
// Maybe refactor as PathVisitor (extended by WF checker)
//public class WFChoicePathChecker extends UnfoldingVisitor<WFChoicePathEnv> //PathCollectionVisitor
////public class WFChoicePathChecker extends InlinedProtocolVisitor<Env<?>>  // FIXME: should be unfolding visitor? GlobalModelBuilder should be too (need a correspondence between syntax nodes and model nodes)
public class WFChoicePathChecker extends ModuleContextVisitor
{
	// N.B. using pointer equality for checking if choice previously visited
	// So UnfoldingVisitor cannot visit a clone
	// equals method identity not suitable unless Ast nodes record additional info like syntactic position
	//private Set<Choice<?>> visited = new HashSet<>();	
	
	public WFChoicePathChecker(Job job)
	{
		super(job);
	}

	@Override
	public void enter(ScribNode parent, ScribNode child) throws ScribbleException
	{
		super.enter(parent, child);
		child.del().enterWFChoicePathCheck(parent, child, this);
	}
	
	@Override
	public ScribNode leave(ScribNode parent, ScribNode child, ScribNode visited) throws ScribbleException
	{
		visited = visited.del().leaveWFChoicePathCheck(parent, child, this, visited);
		return super.leave(parent, child, visited);
	}

	/*@Override
	protected WFChoicePathEnv makeRootProtocolDeclEnv(ProtocolDecl<? extends ProtocolKind> pd)
	{
		return new WFChoicePathEnv();
	}*/

	@Override
	public ScribNode visit(ScribNode parent, ScribNode child) throws ScribbleException
	{
		/*if (child instanceof Choice<?>)
		{
			return visitOverrideForChoice((InteractionSeq<?>) parent, (Choice<?>) child);
		}*/
		if (child instanceof ProtocolDecl<?>)
		{
			if (child instanceof GProtocolDecl)
			{
				return visitOverrideForGProtocolDecl((Module) parent, (GProtocolDecl) child);
			}
			else
			{
				return child;
			}
		}
		else
		{
			return super.visit(parent, child);
		}
	}

	private GProtocolDecl visitOverrideForGProtocolDecl(Module parent, GProtocolDecl child) throws ScribbleException
	{
		GProtocolDecl gpd = (GProtocolDecl) child;
		GModel model = getJobContext().getGlobalModel(gpd.getFullMemberName(parent));

		System.out.println("aaa: " + model);

		HashMap<GModelState, Set<GModelState>> reach = new HashMap<>();
		HashMap<GModelState, Set<GModelState>> invreach = new HashMap<>();
		getReachability(new HashSet<>(), model.init, reach, invreach);
		
		System.out.println("bbb1: " + reach);
		System.out.println("bbb2: " + invreach);
		
		checkWF(new HashSet<>(), model.init, model, reach);
		
		return child;
	}
	
	private static void checkWF(Set<GModelState> seen, GModelState curr, GModel model, Map<GModelState, Set<GModelState>> reach)
	{
		if (seen.contains(curr))
		{
			return;
		}
		Collection<GModelState> succs = curr.getSuccessors();

		if (curr.isChoice())
		{
			Set<GModelPath> paths = new HashSet<>();
			getPaths(paths, new GModelPath(), curr, curr.getChoiceExit(), reach);

			System.out.println("ccc: " + paths);
		}

		seen.add(curr);
		for (GModelState succ : succs)
		{
			checkWF(seen, succ, model, reach);
		}
	}

	// Pre: curr is state at end of path
	private static void getPaths(Set<GModelPath> paths, GModelPath path, GModelState curr, GModelState dest, Map<GModelState, Set<GModelState>> reach)
	{
		for (GModelAction a : curr.getAcceptable())
		{
			GModelState succ = curr.accept(a);
			if (succ.equals(dest))
			{
				paths.add(path.append(a));
			}
			else
			{
				if (reach.get(succ).contains(dest))
				{
					if (!path.containsEdge(a))
					{
						GModelPath tmp = path.append(a);
						getPaths(paths, tmp, succ, dest, reach);
					}
				}
			}
		}
	}
	
	private static void getReachability(Set<GModelState> seen, GModelState curr, Map<GModelState, Set<GModelState>> reach, Map<GModelState, Set<GModelState>> invreach)
	{
		if (seen.contains(curr))
		{
			return;
		}
		Collection<GModelState> succs = curr.getSuccessors();
		for (GModelState succ : succs)
		{
			Set<GModelState> tmp1 = reach.get(curr);
			if (tmp1 == null)
			{
				tmp1 = new HashSet<>();
				reach.put(curr, tmp1);
			}
			tmp1.add(succ);

			Set<GModelState> tmp2 = invreach.get(succ);
			if (tmp2 == null)
			{
				tmp2 = new HashSet<>();
				invreach.put(succ, tmp2);
			}
			tmp2.add(curr);
			
			Set<GModelState> tmp3 = invreach.get(curr);
			if (tmp3 != null)
			{
				for (GModelState s : tmp3)
				{
					tmp2.add(s);
					
					Set<GModelState> tmp4 = reach.get(s);
					if (tmp4 == null)  // Not needed?
					{
						tmp4 = new HashSet<>();
						reach.put(s, tmp4);
					}
					tmp4.add(succ);
				}
			}
			HashSet<GModelState> bar = new HashSet<>(seen);
			bar.add(curr);
			getReachability(bar, succ, reach, invreach);
		}
	}
	
	/*private ScribNode visitOverrideForChoice(InteractionSeq<?> parent, Choice<?> child) throws ScribbleException
	{
		if (child instanceof Choice<?>)
		{
			Choice<?> cho = (Choice<?>) child;
			if (!this.visited.contains(cho))
			{
				this.visited.add(cho);
				//ScribNode n = cho.visitChildren(this);
				ScribNode n = super.visit(parent, child);
				this.visited.remove(cho);
				return n;
			}
			else
			{
				return cho;
			}
		}
		else
		{
			return super.visit(parent, child);
		}
	}
	
	@Override
	protected void unfoldingEnter(ScribNode parent, ScribNode child) throws ScribbleException
	//protected void pathCollectionEnter(ScribNode parent, ScribNode child) throws ScribbleException
	{
		super.unfoldingEnter(parent, child);
		//super.pathCollectionEnter(parent, child);
		child.del().enterWFChoicePathCheck(parent, child, this);
	}
	
	@Override
	protected ScribNode unfoldingLeave(ScribNode parent, ScribNode child, ScribNode visited) throws ScribbleException
	//protected ScribNode pathCollectionLeave(ScribNode parent, ScribNode child, ScribNode visited) throws ScribbleException
	{
		visited = visited.del().leaveWFChoicePathCheck(parent, child, this, visited);
		return super.unfoldingLeave(parent, child, visited);
		//return super.pathCollectionLeave(parent, child, visited);
		/* // NOTE: deviates from standard Visitor pattern: calls super first to collect paths -- maybe refactor more "standard way" by collecting paths in a prior pass and save them in context
		visited = super.pathCollectionLeave(parent, child, visited);
		return visited.del().leaveWFChoicePathCheck(parent, child, this, visited);* /
	}*/
}
