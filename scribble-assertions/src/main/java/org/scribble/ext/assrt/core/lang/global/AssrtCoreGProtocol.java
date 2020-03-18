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
package org.scribble.ext.assrt.core.lang.global;

import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import org.antlr.runtime.tree.CommonTree;
import org.scribble.core.job.Core;
import org.scribble.core.lang.ProtoMod;
import org.scribble.core.lang.SubprotoSig;
import org.scribble.core.lang.global.GProtocol;
import org.scribble.core.lang.local.LProjection;
import org.scribble.core.type.kind.Global;
import org.scribble.core.type.kind.NonRoleParamKind;
import org.scribble.core.type.name.DataName;
import org.scribble.core.type.name.GProtoName;
import org.scribble.core.type.name.LProtoName;
import org.scribble.core.type.name.MemberName;
import org.scribble.core.type.name.RecVar;
import org.scribble.core.type.name.Role;
import org.scribble.core.type.session.global.GSeq;
import org.scribble.core.visit.STypeInliner;
import org.scribble.core.visit.STypeUnfolder;
import org.scribble.core.visit.global.InlinedProjector;
import org.scribble.ext.assrt.core.job.AssrtCore;
import org.scribble.ext.assrt.core.lang.AssrtCoreProtocol;
import org.scribble.ext.assrt.core.lang.local.AssrtCoreLProjection;
import org.scribble.ext.assrt.core.type.formula.AssrtAFormula;
import org.scribble.ext.assrt.core.type.formula.AssrtBFormula;
import org.scribble.ext.assrt.core.type.formula.AssrtTrueFormula;
import org.scribble.ext.assrt.core.type.name.AssrtIntVar;
import org.scribble.ext.assrt.core.type.session.NoSeq;
import org.scribble.ext.assrt.core.type.session.global.AssrtCoreGRec;
import org.scribble.ext.assrt.core.type.session.global.AssrtCoreGType;
import org.scribble.ext.assrt.core.type.session.global.AssrtCoreGTypeFactory;
import org.scribble.ext.assrt.core.type.session.local.AssrtCoreLType;
import org.scribble.ext.assrt.core.visit.global.AssrtCoreGTypeInliner;
import org.scribble.util.ScribException;

public class AssrtCoreGProtocol extends GProtocol
		implements AssrtCoreProtocol<Global, GProtoName, NoSeq<Global>>  // FIXME HACK: Grotocol has GSeq, but here NoSeq
{
	public final AssrtCoreGType type;  // N.B. super.def Seq set to null -- here, body is a "type", not a "seq"
	
	// Cf. AssrtCoreRec
	public final LinkedHashMap<AssrtIntVar, AssrtAFormula> statevars;
	public final AssrtBFormula assertion;  // non-null (True)
	
	// Pre: same keys as statevars
	public final LinkedHashMap<AssrtIntVar, Role> located;  // maps to null for "global" (back compat)

	public AssrtCoreGProtocol(CommonTree source, List<ProtoMod> mods,
			GProtoName fullname, List<Role> rs,
			List<MemberName<? extends NonRoleParamKind>> ps, AssrtCoreGType type,
			LinkedHashMap<AssrtIntVar, AssrtAFormula> svars,
			AssrtBFormula assrt, LinkedHashMap<AssrtIntVar, Role> located)
	{
		super(source, mods, fullname, rs, ps, null);  // N.B. null Seq as super.def
		this.type = type;
		this.statevars = new LinkedHashMap<>(svars);  // TODO: unmod
		this.assertion = assrt;
		this.located = located;
	}

	// Get all var->sort from proto statically -- assumes unique var names
	// Implicit empty context -- cf. AssrtCoreSType#getSortEnv
	public Map<AssrtIntVar, DataName> getSortEnv()
	{
		Map<AssrtIntVar, DataName> sorts = new HashMap<>();
		for (Entry<AssrtIntVar, AssrtAFormula> e : this.statevars.entrySet())
		{
			// statevar sorts -- left-to-right scoping (cf. LinkedHashMap)
			DataName sort = e.getValue().getSort(sorts);
			sorts.put(e.getKey(), sort);
		}
		sorts.putAll(this.type.getBoundSortEnv(sorts));
		return sorts;
	}

	// Deprecated because no longer using GSeq def
	@Override
	public AssrtCoreGProtocol reconstruct(CommonTree source,
			List<ProtoMod> mods, GProtoName fullname, List<Role> rs,
			List<MemberName<? extends NonRoleParamKind>> ps, GSeq def)
	{
		throw new RuntimeException("Deprecated for " + getClass() + ":\n" + def);
	}

	public AssrtCoreGProtocol reconstruct(CommonTree source, List<ProtoMod> mods,
			GProtoName fullname, List<Role> rs,
			List<MemberName<? extends NonRoleParamKind>> ps, AssrtCoreGType type,
			LinkedHashMap<AssrtIntVar, AssrtAFormula> svars, AssrtBFormula ass,
			LinkedHashMap<AssrtIntVar, Role> located)
	{
		return new AssrtCoreGProtocol(source, mods, fullname, rs, ps, type, svars,
				ass, located);
	}
	
	// TODO: N.B. currently, dummy is discarded -- refactor
	// Cf. (e.g.) checkRoleEnabling, that takes Core
	// Pre: stack.peek is the sig for the calling Do (or top-level entry), i.e., it gives the roles/args at the call-site
	@Override
	public AssrtCoreGProtocol getInlined(STypeInliner<Global, GSeq> dummy)
	{
		SubprotoSig sig = new SubprotoSig(this);
		//AssrtCoreGTypeInliner cast = (AssrtCoreGTypeInliner) (STypeInliner<Global, ?>) v;  // CHECKME: cast OK?  no warning?
		AssrtCoreGTypeInliner v = new AssrtCoreGTypeInliner(dummy.core);  // FIXME: doesn't fit visitorfactory pattern, not an GTypeInliner because of NoSeq
		v.pushSig(sig);

		AssrtCoreGType inlined = this.type.inline(v);  
				// CHECKME: refactor type.inline back into visitor pattern?  // No: cannot, because AssrtCoreSTypes do not extend base Choice/etc
		RecVar rv = v.getInlinedRecVar(sig);
		AssrtCoreGTypeFactory tf = (AssrtCoreGTypeFactory) v.core.config.tf.global;
		AssrtCoreGRec rec = tf.AssrtCoreGRec(null, rv, inlined,
				//new LinkedHashMap<>(), AssrtTrueFormula.TRUE, new LinkedHashMap<>());
				this.statevars, this.assertion, this.located);
		AssrtCoreGType pruned = rec.pruneRecs((AssrtCore) v.core);  // Empty statevars/located here; recorded by parent proto

		// TODO
		/*Set<Role> used = rec.gather(new RoleGatherer<Global, GSeq>()::visit) .collect(Collectors.toSet());
		List<Role> rs = this.roles.stream().filter(x -> used.contains(x))  // Prune role decls -- CHECKME: what is an example?  was this from before unused role checking?
				.collect(Collectors.toList());*/
		return new AssrtCoreGProtocol(getSource(), this.mods, this.fullname,
				this.roles, this.params, pruned,
		//new LinkedHashMap<>(), AssrtTrueFormula.TRUE, new LinkedHashMap<>());
				this.statevars, this.assertion, this.located);  // FIXME: ^refactor statevars/located properly with above rec, currently duplicated
	}
	
	@Override
	public AssrtCoreGProtocol unfoldAllOnce(STypeUnfolder<Global, GSeq> v)
	{
		throw new RuntimeException("Deprecated for " + getClass() + ":\n" + this);
	}

	@Override
	public void checkRoleEnabling(Core core) throws ScribException
	{
		throw new RuntimeException("Deprecated for " + getClass() + ":\n" + this);
	}

	@Override
	public void checkExtChoiceConsistency(Core core) throws ScribException
	{
		throw new RuntimeException("Deprecated for " + getClass() + ":\n" + this);
	}

	@Override
	public void checkConnectedness(Core core, boolean implicit)
			throws ScribException
	{
		throw new RuntimeException("Deprecated for " + getClass() + ":\n" + this);
	}
	
	// FIXME: return type (AssrtCoreLProjection doesn't extend AssrtCoreLProtocol), cf. CoreContext G/LProtocol hardcoding
	@Override
	public AssrtCoreLProjection projectInlined(Core core, Role self)
	{
		Map<Role, Set<AssrtIntVar>> known = new HashMap<>();
		this.roles.forEach(x -> known.put(x, this.located.entrySet().stream()
				.filter(y ->
					{
						Role r = y.getValue();
						return r == null || r.equals(x);
					})
				.map(y -> y.getKey())
				.collect(Collectors.toSet())));  // FIXME? will be overwritten by inserted top-level rec anway

		AssrtCoreLType proj = this.type.projectInlined((AssrtCore) core, self,
				AssrtTrueFormula.TRUE, known, Collections.emptyMap());
		LProtoName fullname = InlinedProjector
				.getFullProjectionName(this.fullname, self);

		LinkedHashMap<AssrtIntVar, AssrtAFormula> svars = new LinkedHashMap<>();  // Corresponds to known, but need LinkedHashMap here
		this.statevars.entrySet().stream()  // ordered
				.filter(x ->
					{
						Role r = this.located.get(x.getKey());
						return r == null || r.equals(self);
					})
				.forEach(x -> svars.put(x.getKey(), x.getValue()));

		return new AssrtCoreLProjection(this.mods, fullname, this.roles, self,
				this.params, this.fullname, proj, svars, this.assertion);
	}

	// N.B. no "fixing" passes done here -- need breadth-first passes to be sequentialised for subproto visiting
	@Override
	public LProjection project(Core core, Role self)
	{
		throw new RuntimeException("Deprecated for " + getClass() + ":\n" + this);
	}
	
	@Override
	public String toString()
	{
		//return super.toString();  // No: super.def == null
		return "global protocol " + this.fullname.getSimpleName()
				+ paramsToString()
				+ rolesToString()
				+ " @<"
				+ this.statevars.entrySet().stream()
						.map(x -> x.getKey()
								+ (this.located.get(x.getKey()) == null
										? " :"
										: ":" + this.located.get(x.getKey()) + " ")
								+ "= " + x.getValue())
						.collect(Collectors.joining(", "))
				+ "> " + this.assertion
				+ " {\n" + this.type + "\n}";
	}

	@Override
	public int hashCode()
	{
		int hash = 25799;
		//hash = 31 * hash + super.hashCode();  // No: super.def == null
		hash = 31 * hash + this.mods.hashCode();
		hash = 31 * hash + this.fullname.hashCode();
		hash = 31 * hash + this.roles.hashCode();
		hash = 31 * hash + this.params.hashCode();
		hash = 31 * hash + this.type.hashCode();
		hash = 31 * hash + this.statevars.hashCode();
		hash = 31 * hash + this.assertion.hashCode();
		hash = 31 * hash + this.located.hashCode();
		return hash;
	}

	@Override
	public boolean equals(Object o)
	{
		if (this == o)
		{
			return true;
		}
		if (!(o instanceof AssrtCoreGProtocol))
		{
			return false;
		}
		//return super.equals(o);  // Does canEquals  // No: super.def == null
		AssrtCoreGProtocol them = (AssrtCoreGProtocol) o;
		return them.canEquals(this) && this.mods.equals(them.mods)
				&& this.fullname.equals(them.fullname) && this.roles.equals(them.roles)
				&& this.params.equals(them.params) && this.type.equals(them.type)
				&& this.statevars.equals(them.statevars)
				&& this.assertion.equals(them.assertion)
				&& this.located.equals(them.located);
	}

	@Override
	public boolean canEquals(Object o)
	{
		return o instanceof AssrtCoreGProtocol;
	}
}
