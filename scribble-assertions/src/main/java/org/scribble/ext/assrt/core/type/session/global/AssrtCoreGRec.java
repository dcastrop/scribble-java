package org.scribble.ext.assrt.core.type.session.global;

import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import org.antlr.runtime.tree.CommonTree;
import org.scribble.core.type.kind.Global;
import org.scribble.core.type.kind.Local;
import org.scribble.core.type.name.DataName;
import org.scribble.core.type.name.RecVar;
import org.scribble.core.type.name.Role;
import org.scribble.core.type.name.Substitutions;
import org.scribble.ext.assrt.core.job.AssrtCore;
import org.scribble.ext.assrt.core.type.formula.AssrtAFormula;
import org.scribble.ext.assrt.core.type.formula.AssrtBFormula;
import org.scribble.ext.assrt.core.type.name.AssrtAnnotDataName;
import org.scribble.ext.assrt.core.type.name.AssrtIntVar;
import org.scribble.ext.assrt.core.type.session.AssrtCoreRec;
import org.scribble.ext.assrt.core.type.session.AssrtCoreSyntaxException;
import org.scribble.ext.assrt.core.type.session.local.AssrtCoreLEnd;
import org.scribble.ext.assrt.core.type.session.local.AssrtCoreLRecVar;
import org.scribble.ext.assrt.core.type.session.local.AssrtCoreLType;
import org.scribble.ext.assrt.core.type.session.local.AssrtCoreLTypeFactory;
import org.scribble.ext.assrt.core.visit.gather.AssrtCoreRecVarGatherer;
import org.scribble.ext.assrt.core.visit.gather.AssrtCoreStateVarGatherer;
import org.scribble.ext.assrt.core.visit.global.AssrtCoreGTypeInliner;

public class AssrtCoreGRec extends AssrtCoreRec<Global, AssrtCoreGType>
		implements AssrtCoreGType
{
	protected AssrtCoreGRec(CommonTree source, RecVar rv, AssrtCoreGType body,
			LinkedHashMap<AssrtIntVar, AssrtAFormula> svars, AssrtBFormula ass)
	{
		super(source, rv, body, svars, ass);
	}

	@Override
	public AssrtCoreGType disamb(AssrtCore core, Map<AssrtIntVar, DataName> env)
	{
		Map<AssrtIntVar, DataName> env1 = new HashMap<>(env);
		this.statevars.entrySet()
				.forEach(x -> env1.put(x.getKey(), x.getValue().getSort(env1)));
		LinkedHashMap<AssrtIntVar, AssrtAFormula> svars = new LinkedHashMap<>();
		this.statevars.entrySet().forEach(x -> svars.put(x.getKey(),
				(AssrtAFormula) x.getValue().disamb(env1)));  // Unnecessary, disallow mutual var refs?
		return ((AssrtCoreGTypeFactory) core.config.tf.global).AssrtCoreGRec(
				getSource(), this.recvar, this.body.disamb(core, env1), svars,
				(AssrtBFormula) this.assertion.disamb(env1));
	}

	@Override
	public AssrtCoreGType substitute(AssrtCore core, Substitutions subs)
	{
		return ((AssrtCoreGTypeFactory) core.config.tf.global).AssrtCoreGRec(
				getSource(), this.recvar, this.body.substitute(core, subs), this.statevars,
				this.assertion);
	}

	@Override
	public AssrtCoreGType inline(AssrtCoreGTypeInliner v)
	{
		throw new RuntimeException("[TODO] :\n" + this);
	}

	@Override
	public AssrtCoreGType pruneRecs(AssrtCore core)
	{
		Set<RecVar> rvs = this.body
				.assrtCoreGather(  // TODO: factor out with base gatherer
						new AssrtCoreRecVarGatherer<Global, AssrtCoreGType>()::visit)
				.collect(Collectors.toSet());
		return rvs.contains(this.recvar) ? this : this.body;
	}

	@Override
	public AssrtCoreLType projectInlined(AssrtCore core, Role self,
			AssrtBFormula f, Map<RecVar, List<AssrtIntVar>> svars,
			Set<AssrtIntVar> seenSvars) throws AssrtCoreSyntaxException
	{
		Map<RecVar, List<AssrtIntVar>> svars1 = new HashMap<>(svars);
		svars1.put(this.recvar,
				this.statevars.keySet().stream().collect(Collectors.toList()));

		Set<AssrtIntVar> seenSvars1 = Stream
				.concat(seenSvars.stream(),
						this.statevars.values().stream()
								.flatMap(x -> x.getIntVars().stream()))
				.collect(Collectors.toSet());

		AssrtCoreLType proj = this.body.projectInlined(core, self, f, svars1,
				seenSvars1);

		//System.out.println("2222: " + this + " ,, " + this.statevars.keySet());
		Set<AssrtIntVar> foo = proj.assrtCoreGather(
				new AssrtCoreStateVarGatherer<Local, AssrtCoreLType>(
						this.statevars.keySet())::visit)
				.collect(Collectors.toSet());
		System.out.println("2222: " + foo);
		
		LinkedHashMap<AssrtIntVar, AssrtAFormula> tmp = new LinkedHashMap<>();
		this.statevars.entrySet().stream().forEach(x ->
			{
				AssrtIntVar key = x.getKey();
				if (foo.contains(key))
				{
					tmp.put(key, x.getValue());
				}
			});
	
		...HERE: "project" this.assertion?

		return (proj instanceof AssrtCoreLRecVar) 
				? AssrtCoreLEnd.END
				: ((AssrtCoreLTypeFactory) core.config.tf.local).AssrtCoreLRec(null,
						this.recvar, tmp, proj, this.assertion);
	}

	@Override
	public List<AssrtAnnotDataName> collectAnnotDataVarDecls(
			Map<AssrtIntVar, DataName> env)
	{
		List<AssrtAnnotDataName> res = new LinkedList<>();
		Map<AssrtIntVar, DataName> env1 = new HashMap<>(env);
		this.statevars.entrySet()
				.forEach(x -> env1.put(x.getKey(), x.getValue().getSort(env1)));

		this.statevars.keySet().stream().forEachOrdered(
				v -> res.add(new AssrtAnnotDataName(v, env1.get(v))));
		/*this.ass.getIntVars().stream().forEachOrdered(
				v -> res.add(new AssrtAnnotDataType(v, new DataType("int"))));  // No: not decls*/

		res.addAll(this.body.collectAnnotDataVarDecls(env1));
		return res;
	}

	@Override
	public boolean equals(Object obj)
	{
		if (this == obj)
		{
			return true;
		}
		if (!(obj instanceof AssrtCoreGRec))
		{
			return false;
		}
		return super.equals(obj);  // Does canEquals
	}
	
	@Override
	public boolean canEquals(Object o)
	{
		return o instanceof AssrtCoreGRec;
	}
	
	@Override
	public int hashCode()
	{
		int hash = 2333;
		hash = 31 * hash + super.hashCode();
		return hash;
	}
}
