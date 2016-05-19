package org.scribble.model.global;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;

import org.scribble.model.ModelAction;
import org.scribble.model.local.IOAction;
import org.scribble.model.local.Receive;
import org.scribble.model.local.Send;
import org.scribble.sesstype.Payload;
import org.scribble.sesstype.kind.Global;
import org.scribble.sesstype.name.MessageId;
import org.scribble.sesstype.name.Role;

// Mutable
public class GModelAction extends ModelAction<Global> //implements PathElement
{
	//private static int counter = 1;

	//public final int id;
	public final Role src;
	public final Role dest;
	//public final IOAction action;

	//private Set<GModelAction> deps = new HashSet<>();
	
	//public GModelAction(Role src, IOAction action)
	public GModelAction(Role src, Role dest, MessageId<?> mid, Payload payload)
	//public ModelAction(Role peer, MessageId mid)  // Should be a send/receive
	{
		/*this.id = counter++;
		this.src = src;
		this.action = action;*/
		super(dest, mid, payload);
		this.dest = dest;
		this.src = src;
	}
	
	public Set<Role> getRoles()
	{
		//return Arrays.stream(new Role[] {this.src, this.dest}).collect(Collectors.toSet());
		return new HashSet<>(Arrays.asList(this.src, this.dest));
	}
	
	public boolean containsRole(Role role)
	{
		return this.src.equals(role) || this.dest.equals(role);
	}
	
	public IOAction project(Role self)
	{
		if (this.src.equals(self))
		{
			if (this.dest.equals(self))
			{
				throw new RuntimeException("TODO: " + this);
			}
			else
			{
				return new Send(this.dest, this.mid, this.payload);
			}
		}
		else
		{
			if (this.dest.equals(self))
			{
				return new Receive(this.src, this.mid, this.payload);
			}
			else
			{
				return null;  // FIXME?
			}
		}
	}
	
	/*public void addDependency(GModelAction ma)
	{
		this.deps.add(ma);
	}
	
	public Set<GModelAction> getDependencies()
	{
		return this.deps;
	}
	
	public boolean isDependentOn(GModelAction ma)
	{
		return this.deps.contains(ma);
	}*/
	
	/*@Override
	public int hashCode()
	{
		//return 827 * this.id;
		return 827 * this.src.hashCode() + super.hashCode();
	}*/
	
	/*@Override
	public boolean equals(Object o)
	{
		if (this == o)
		{
			return true;
		}
		if (!(o instanceof GModelAction))
		{
			return false;
		}
		GModelAction tmp = (GModelAction) o;
		//return this.id == ((GModelAction) o).id;
		return tmp.canEqual(this) && tmp.src.equals(this.src) && super.equals(o);
	}*/

	@Override
	public String toString()
	{
		//return this.id + ":" + this.src + ":" + this.action + " " + this.deps.stream().map((d) -> d.id).collect(Collectors.toList());
		return this.src + "->" + super.toString();
	}

	@Override
	protected String getCommSymbol()
	{
		return ": ";
	}

	@Override
	public boolean canEqual(Object o)
	{
		return o instanceof GModelAction;
	}
}