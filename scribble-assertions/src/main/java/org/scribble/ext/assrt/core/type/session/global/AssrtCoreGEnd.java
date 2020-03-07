package org.scribble.ext.assrt.core.type.session.global;

import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.scribble.core.type.kind.Global;
import org.scribble.core.type.name.DataName;
import org.scribble.core.type.name.RecVar;
import org.scribble.core.type.name.Role;
import org.scribble.core.type.name.Substitutions;
import org.scribble.ext.assrt.core.job.AssrtCore;
import org.scribble.ext.assrt.core.type.formula.AssrtBFormula;
import org.scribble.ext.assrt.core.type.name.AssrtAnnotDataName;
import org.scribble.ext.assrt.core.type.name.AssrtIntVar;
import org.scribble.ext.assrt.core.type.session.AssrtCoreEnd;
import org.scribble.ext.assrt.core.type.session.local.AssrtCoreLEnd;
import org.scribble.ext.assrt.core.type.session.local.AssrtCoreLTypeFactory;
import org.scribble.ext.assrt.core.visit.global.AssrtCoreGTypeInliner;


public class AssrtCoreGEnd extends AssrtCoreEnd<Global, AssrtCoreGType>
		implements AssrtCoreGType
{
	public static final AssrtCoreGEnd END = new AssrtCoreGEnd();
	
	protected AssrtCoreGEnd()
	{
		
	}

	@Override
	public AssrtCoreGType disamb(AssrtCore core, Map<AssrtIntVar, DataName> env)
	{
		return this;
	}

	@Override
	public AssrtCoreGType substitute(AssrtCore core, Substitutions subs)
	{
		return this;
	}

	@Override
	public AssrtCoreGType inline(AssrtCoreGTypeInliner v)
	{
		return this;
	}

	@Override
	public AssrtCoreGType pruneRecs(AssrtCore core)
	{
		return this;
	}

	@Override
	public AssrtCoreLEnd projectInlined(AssrtCore core, Role self,
			AssrtBFormula f, Map<RecVar, List<AssrtIntVar>> svars,
			Set<AssrtIntVar> seenSvars)
	{
		return ((AssrtCoreLTypeFactory) core.config.tf.local).AssrtCoreLEnd();
	}

	@Override
	public List<AssrtAnnotDataName> collectAnnotDataVarDecls(
			Map<AssrtIntVar, DataName> env)
	{
		return Collections.emptyList();
	}
	
	@Override
	public boolean equals(Object obj)
	{
		if (!(obj instanceof AssrtCoreGEnd))
		{
			return false;
		}
		return super.equals(obj);  // Checks canEquals
	}
	
	@Override
	public boolean canEquals(Object o)
	{
		return o instanceof AssrtCoreGEnd;
	}

	@Override
	public int hashCode()
	{
		return 31*2381;
	}
}
