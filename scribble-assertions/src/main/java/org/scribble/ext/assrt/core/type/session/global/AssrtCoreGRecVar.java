package org.scribble.ext.assrt.core.type.session.global;

import java.util.Collections;
import java.util.List;

import org.scribble.ext.assrt.core.type.formula.AssrtArithFormula;
import org.scribble.ext.assrt.core.type.formula.AssrtBoolFormula;
import org.scribble.ext.assrt.core.type.name.AssrtAnnotDataType;
import org.scribble.ext.assrt.core.type.session.AssrtCoreAstFactory;
import org.scribble.ext.assrt.core.type.session.AssrtCoreRecVar;
import org.scribble.ext.assrt.core.type.session.local.AssrtCoreLRecVar;
import org.scribble.type.name.RecVar;
import org.scribble.type.name.Role;

	
// FIXME: hashCode/equals
public class AssrtCoreGRecVar extends AssrtCoreRecVar implements AssrtCoreGType
{
	//public AssrtCoreGRecVar(RecVar var, AssrtArithFormula expr)
	public AssrtCoreGRecVar(RecVar var, List<AssrtArithFormula> annotexprs)
	{
		super(var, annotexprs);
	}

	@Override
	public List<AssrtAnnotDataType> collectAnnotDataTypeVarDecls()
	{
		return Collections.emptyList();
	}

	@Override
	public AssrtCoreLRecVar project(AssrtCoreAstFactory af, Role r, AssrtBoolFormula f)
	{
		return af.AssrtCoreLRecVar(this.recvar, this.annotexprs);
	}

	@Override
	public boolean equals(Object obj)
	{
		if (!(obj instanceof AssrtCoreGRecVar))
		{
			return false;
		}
		return super.equals(obj);  // Does canEquals
	}

	@Override
	public int hashCode()
	{
		int hash = 2411;
		hash = 31*hash + super.hashCode();
		return hash;
	}
	
	@Override
	public boolean canEquals(Object o)
	{
		return o instanceof AssrtCoreGRecVar;
	}
}