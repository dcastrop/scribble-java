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
package org.scribble.ext.assrt.core.visit.gather;

import java.util.Collections;
import java.util.Set;
import java.util.stream.Stream;

import org.scribble.core.type.kind.ProtoKind;
import org.scribble.ext.assrt.core.type.name.AssrtIntVar;
import org.scribble.ext.assrt.core.type.session.AssrtCoreChoice;
import org.scribble.ext.assrt.core.type.session.AssrtCoreRec;
import org.scribble.ext.assrt.core.type.session.AssrtCoreSType;

public class AssrtCoreStateVarGatherer<K extends ProtoKind, 
			B extends AssrtCoreSType<K, B>>
		extends AssrtCoreSTypeGatherer<K, B, AssrtIntVar>
{
	private final Set<AssrtIntVar> svars;

	public AssrtCoreStateVarGatherer(Set<AssrtIntVar> svars)
	{
		this.svars = Collections.unmodifiableSet(svars);
	}

	@Override
	public Stream<AssrtIntVar> visitChoice(AssrtCoreChoice<K, B> n)
	{
		return n.cases.keySet().stream()
				.flatMap(x -> x.ass.getIntVars().stream()
						.filter(y -> this.svars.contains(y)));
	}

	@Override
	public Stream<AssrtIntVar> visitRec(AssrtCoreRec<K, B> n)
	{
		Stream<AssrtIntVar> res = n.statevars.values().stream()
				.flatMap(x -> x.getIntVars().stream()
						.filter(y -> this.svars.contains(y)));
		return Stream.concat(res, n.assertion.getIntVars().stream()
				.filter(x -> this.svars.contains(x)));
	}

	/*@Override
	public Stream<AssrtIntVar> visitRecVar(AssrtCoreRecVar<K, B> n)
	{
		return n.stateexprs.stream()
				.flatMap(x -> x.getIntVars().stream()
						.filter(y -> this.svars.contains(y)));
	}*/
}
