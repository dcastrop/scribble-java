package org.scribble.ext.go.core.ast.local;

import java.util.Collections;
import java.util.Set;

import org.scribble.ext.go.core.ast.RPCoreAstFactory;
import org.scribble.ext.go.core.ast.RPCoreRecVar;
import org.scribble.ext.go.core.ast.RPCoreType;
import org.scribble.ext.go.core.type.RPRoleVariant;
import org.scribble.ext.go.type.index.RPIndexVar;
import org.scribble.type.kind.Local;
import org.scribble.type.name.RecVar;

	
public class RPCoreLRecVar extends RPCoreRecVar<Local> implements RPCoreLType
{
	public RPCoreLRecVar(RecVar var)
	{
		super(var);
	}

	@Override
	public RPCoreLType minimise(RPCoreAstFactory af, RPRoleVariant subj)
	{
		return this;
	}
	
	@Override
	public RPCoreLType subs(RPCoreAstFactory af, RPCoreType<Local> old, RPCoreType<Local> neu) 
	{
		if (this.equals(old))  // Shouldn't happen?
		{
			return (RPCoreLType) neu;
		}
		return this;
	}
	
	@Override
	public Set<RPIndexVar> getIndexVars()
	{
		return Collections.emptySet();
	}

	@Override
	public boolean equals(Object obj)
	{
		if (!(obj instanceof RPCoreLRecVar))
		{
			return false;
		}
		return super.equals(obj);  // Does canEquals
	}

	@Override
	public int hashCode()
	{
		int hash = 2417;
		hash = 31*hash + super.hashCode();
		return hash;
	}
	
	@Override
	public boolean canEquals(Object o)
	{
		return o instanceof RPCoreLRecVar;
	}
}