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
package org.scribble.ext.assrt.model.endpoint;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import org.scribble.ext.assrt.type.formula.AssrtArithFormula;
import org.scribble.ext.assrt.type.name.AssrtDataTypeVar;
import org.scribble.model.MState;
import org.scribble.model.endpoint.EModelFactory;
import org.scribble.model.endpoint.EState;
import org.scribble.model.endpoint.actions.EAction;
import org.scribble.type.name.RecVar;

public class AssrtEState extends EState
{
	private final Map<AssrtDataTypeVar, AssrtArithFormula> statevars; // Note: even with syntactic single var per rec, nested recs can lead to mulitple vars per state

	// FIXME: make AssrtIntTypeVar?
	protected AssrtEState(Set<RecVar> labs, Map<AssrtDataTypeVar, AssrtArithFormula> vars)  // FIXME: currently syntactically restricted to one annot var
	{
		super(labs);
		//this.vars = Collections.unmodifiableMap(vars);
		this.statevars = new HashMap<>(vars);  // Side effected by addStateVars
	}
	
	@Override
	protected AssrtEState cloneNode(EModelFactory ef, Set<RecVar> labs)
	{
		return ((AssrtEModelFactory) ef).newAssrtEState(labs, this.statevars);
	}
	
	public Map<AssrtDataTypeVar, AssrtArithFormula> getStateVars()
	{
		return this.statevars;
	}

	// For public access, do via AssrtEGraphBuilderUtil
	protected final void addStateVars(Map<AssrtDataTypeVar, AssrtArithFormula> vars)
	{
		this.statevars.putAll(vars);
	}

	@Override
	protected String getNodeLabel()
	{
		String labs = this.labs.toString();
		return "label=\"" + this.id + ": " + labs.substring(1, labs.length() - 1) + ", " + this.statevars + "\"";  // FIXME: would be more convenient for this method to return only the label body
	}
	
	@Override
	public AssrtEState getSuccessor(EAction a)
	{
		return (AssrtEState) super.getSuccessor(a);
	}
	
	@Override
	public int hashCode()
	{
		int hash = 6619;
		hash = 31 * hash + super.hashCode();  // N.B. uses state ID only -- following super pattern
		hash = 31 * hash + this.statevars.hashCode();  // N.B. uses state ID only -- following super pattern
		return hash;
	}

	@Override
	public boolean equals(Object o)
	{
		if (this == o)
		{
			return true;
		}
		if (!(o instanceof AssrtEState))
		{
			return false;
		}
		return super.equals(o) && this.statevars.equals(((AssrtEState) o).statevars);  // Checks canEquals
	}

	@Override
	protected boolean canEquals(MState<?, ?, ?, ?> s)
	{
		return s instanceof AssrtEState;
	}
}