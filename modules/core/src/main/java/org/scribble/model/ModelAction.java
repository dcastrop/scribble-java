package org.scribble.model;

import org.scribble.sesstype.Payload;
import org.scribble.sesstype.kind.ProtocolKind;
import org.scribble.sesstype.name.MessageId;
import org.scribble.sesstype.name.Role;

public abstract class ModelAction<K extends ProtocolKind>
{
	private static int count = 0;
	
	public final int id;
	
	public final Role obj;
	public final MessageId<?> mid;
	public final Payload payload;  // Empty for MessageSigNames
	
	public ModelAction(Role peer, MessageId<?> mid, Payload payload)
	{
		this.id = ModelAction.count++;

		this.obj = peer;
		this.mid = mid;
		this.payload = payload;
	}
	
	@Override
	public String toString()
	{
		return this.obj + getCommSymbol() + this.mid + this.payload;
	}
	
	protected abstract String getCommSymbol();
	
	/*@Override
	public int hashCode()
	{
		int hash = 919;
		hash = 31 * hash + this.peer.hashCode();
		hash = 31 * hash + this.mid.hashCode();
		hash = 31 * hash + this.payload.hashCode();
		return hash;
	}*/

	@Override
	public final int hashCode()
	{
		int hash = 79;
		hash = 31 * hash + this.id;
		return hash;
	}

	@Override
	public boolean equals(Object o)  // FIXME: kind
	{
		if (this == o)
		{
			return true;
		}
		if (!(o instanceof ModelAction))
		{
			return false;
		}
		/*ModelAction<?> a = (ModelAction<?>) o;  // Refactor as "compatible"
		return a.canEqual(this) && 
				this.peer.equals(a.peer) && this.mid.equals(a.mid) && this.payload.equals(a.payload);*/
		return this.id == ((ModelAction<?>) o).id;
	}
	
	public abstract boolean canEqual(Object o);
}