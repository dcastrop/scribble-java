package org.scribble.ext.go.core.ast.global;

import java.util.Collections;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import org.scribble.ast.global.GProtocolDecl;
import org.scribble.ext.go.core.ast.RPCoreAstFactory;
import org.scribble.ext.go.core.ast.RPCoreForeach;
import org.scribble.ext.go.core.ast.RPCoreSyntaxException;
import org.scribble.ext.go.core.ast.RPCoreType;
import org.scribble.ext.go.core.ast.local.RPCoreLEnd;
import org.scribble.ext.go.core.ast.local.RPCoreLType;
import org.scribble.ext.go.core.type.RPIndexedRole;
import org.scribble.ext.go.core.type.RPInterval;
import org.scribble.ext.go.core.type.RPRoleVariant;
import org.scribble.ext.go.main.GoJob;
import org.scribble.ext.go.type.index.RPIndexExpr;
import org.scribble.ext.go.type.index.RPIndexVar;
import org.scribble.type.kind.Global;
import org.scribble.type.name.Role;

public class RPCoreGForeach extends RPCoreForeach<RPCoreGType, Global> implements RPCoreGType
{
	public RPCoreGForeach(Role role, RPIndexVar var, RPIndexExpr start, RPIndexExpr end, RPCoreGType body, RPCoreGType seq)
	{
		super(role, var, start, end, body, seq);
	}
	
	@Override
	public RPCoreGType subs(RPCoreAstFactory af, RPCoreType<Global> old, RPCoreType<Global> neu)
	{
		if (this.equals(old))
		{
			return (RPCoreGType) neu;
		}
		else
		{
			return af.RPCoreGForeach(this.role, this.var, this.start, this.end,
					this.body.subs(af, old, neu), this.seq.subs(af, old, neu));
		}
	}
	
	@Override
	public boolean isWellFormed(GoJob job, GProtocolDecl gpd)
	{
		// FIXME TODO: interval constraints, nested foreach constraints, etc. -- cf. RPCoreGChoice
		return this.body.isWellFormed(job, gpd);
	}
	
	@Override
	public Set<RPIndexedRole> getIndexedRoles()  // cf. RPForeachDel#leaveIndexVarCollection (though not currently used)
	{
		Set<RPInterval> d = Stream.of(new RPInterval(this.start, this.end)).collect(Collectors.toSet());
		Set<RPInterval> var = Stream.of(new RPInterval(this.var, this.var)).collect(Collectors.toSet());
		Set<RPIndexedRole> irs = this.body.getIndexedRoles()
				.stream().map(
						ir -> ir.intervals.equals(var)
								? new RPIndexedRole(ir.getName().toString(), d)
								: ir
				).collect(Collectors.toSet());
		return irs;
	}

	@Override
	//public ParamCoreLType project(ParamCoreAstFactory af, Role r, Set<ParamRange> ranges) throws ParamCoreSyntaxException
	public RPCoreLType project(RPCoreAstFactory af, RPRoleVariant subj) throws RPCoreSyntaxException
	{
		RPCoreLType seq = this.seq.project(af, subj);

		RPInterval v = new RPInterval(this.start, this.end);
		if (subj.getName().equals(this.role) && subj.intervals.contains(v))  // FIXME: proper interval inclusion? -- also RPCoreGChoice#project?
				// FIXME: factor out  // cf. RPCoreGChoice#project
		{
			RPRoleVariant indexed = new RPRoleVariant(subj.getName().toString(),
					Stream.of(new RPInterval(this.var, this.var)).collect(Collectors.toSet()), Collections.emptySet());
			RPCoreLType body = this.body.project(af, indexed);
			return body.subs(af, RPCoreLEnd.END, seq);
		}
		/*else if ()
		{
			// ...else substitute cont for end in body
		}*/
		else 
		{
			RPCoreLType body = this.body.project(af, subj);
			return af.RPCoreLForeach(subj, this.var, this.start, this.end, body, seq);
			//throw new RuntimeException("[rp-core] TODO: " + this + " project onto " + subj);
		}
	}

	@Override
	public boolean equals(Object obj)
	{
		if (this == obj)
		{
			return true;
		}
		if (!(obj instanceof RPCoreGForeach))
		{
			return false;
		}
		return super.equals(obj);  // Does canEquals
	}
	
	@Override
	public boolean canEquals(Object o)
	{
		return o instanceof RPCoreGForeach;
	}
	
	@Override
	public int hashCode()
	{
		int hash = 4273;
		hash = 31 * hash + super.hashCode();
		return hash;
	}
}
