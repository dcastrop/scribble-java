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
package org.scribble.ext.assrt.ast;

import java.util.List;
import java.util.stream.Collectors;

import org.antlr.runtime.Token;
import org.scribble.ast.ParamDecl;
import org.scribble.ast.ParamDeclList;
import org.scribble.ast.name.simple.RoleNode;
import org.scribble.del.DelFactory;
import org.scribble.ext.assrt.core.type.kind.AssrtIntVarKind;
import org.scribble.ext.assrt.del.AssrtDelFactory;
import org.scribble.util.ScribException;
import org.scribble.visit.AstVisitor;


public class AssrtLocatedStateVarDeclList extends ParamDeclList<AssrtIntVarKind>
{
	// ScribTreeAdaptor#create constructor
	public AssrtLocatedStateVarDeclList(Token t)
	{
		super(t);
	}

	// Tree#dupNode constructor
	public AssrtLocatedStateVarDeclList(AssrtLocatedStateVarDeclList node)
	{
		super(node);
	}

	public RoleNode getRoleChild()  // TODO refactor
	{
		return (RoleNode) getChild(0);
	}

	@Override
	public List<AssrtStateVarDecl> getDeclChildren()
	{
		return getChildren().stream()
				.skip(1)
				.limit(getChildCount() - 2)
				.map(x -> (AssrtStateVarDecl) x)
				.collect(Collectors.toList());
	}

	// N.B. currently mandatory -- TODO FIXME
	public AssrtBExprNode getAnnotAssertChild()  // Cf. AssrtGProtoHeader
	{
		return (AssrtBExprNode) getChild(getChildCount() - 1);
	}

	/*public List<AssrtIntVar> getIntVars()
	{
		return getDeclChildren().stream().map(x -> x.getDeclName())
				.collect(Collectors.toList());
	}*/

	@Override
	public void addScribChildren(
			List<? extends ParamDecl<? extends AssrtIntVarKind>> ds)
	{
		throw new RuntimeException("Shouldn't get in here: " + this);
	}

	// "add", not "set"
	public void addScribChildren(RoleNode role, List<AssrtStateVarDecl> ds,
			AssrtBExprNode bexpr)
	{
		// Cf. above getters and Scribble.g children order
		super.addChild(role);
		super.addChildren(ds);
		super.addChild(bexpr);
	}
	
	@Override
	public AssrtLocatedStateVarDeclList dupNode()
	{
		return new AssrtLocatedStateVarDeclList(this);
	}

	@Override
	public ParamDeclList<AssrtIntVarKind> reconstruct(
			List<? extends ParamDecl<AssrtIntVarKind>> ds)
	{
		throw new RuntimeException("Shouldn't get in here: " + this);
	}
	
	public AssrtLocatedStateVarDeclList reconstruct(
			RoleNode role, List<AssrtStateVarDecl> ds, AssrtBExprNode bexpr)
	{
		AssrtLocatedStateVarDeclList dup = dupNode();
		dup.addScribChildren(role, ds, bexpr);
		dup.setDel(del());  // No copy
		return dup;
	}

	@Override
	public AssrtLocatedStateVarDeclList visitChildren(AstVisitor v)
			throws ScribException
	{
		RoleNode role = (RoleNode) visitChild(getRoleChild(), v);
		List<AssrtStateVarDecl> ps = visitChildListWithClassEqualityCheck(this,
				getDeclChildren(), v);
		AssrtBExprNode ass = getAnnotAssertChild();
		if (ass != null)
		{
			ass = (AssrtBExprNode) visitChild(ass, v);
		}
		return reconstruct(role, ps, ass);
	}

	@Override
	public void decorateDel(DelFactory df)
	{
		((AssrtDelFactory) df).AssrtLocatedStateVarDeclList(this);
	}

	@Override
	public String toString()
	{
		return getRoleChild() + "<" + super.toString() + ">"
				+ getAnnotAssertChild();
	}
}

/*public abstract class AssrtStateVarDeclList extends ScribNodeBase 
{
	// ScribTreeAdaptor#create constructor
	public AssrtStateVarDeclList(Token t)
	{
		super(t);
	}

	// Tree#dupNode constructor
	public AssrtStateVarDeclList(AssrtStateVarDeclList node)
	{
		super(node);
	}
	
	public abstract List<? extends AssrtStateVarDecl> getDeclChildren();

	// "add", not "set"
	public void addScribChildren(List<? extends AssrtStateVarDecl> ds)
	{
		// Cf. above getters and Scribble.g children order
		super.addChildren(ds);
	}
	
	@Override
	public abstract AssrtStateVarDeclList dupNode();
	
	public AssrtStateVarDeclList reconstruct(
			List<? extends AssrtStateVarDecl> ds)
	{
		AssrtStateVarDeclList dup = dupNode();
		dup.addScribChildren(ds);
		dup.setDel(del());  // No copy
		return dup;
	}
	
	@Override
	public AssrtStateVarDeclList visitChildren(AstVisitor v)
			throws ScribException
	{
		List<? extends AssrtStateVarDecl> ps = 
				visitChildListWithClassEqualityCheck(this, getDeclChildren(), v);
		return reconstruct(ps);
	}
		
	public final int length()
	{
		return getDeclChildren().size();
	}

	public final boolean isEmpty()
	{
		return length() == 0;
	}

	// Without enclosing braces -- added by subclasses
	@Override
	public String toString()
	{
		return getDeclChildren().stream().map(x -> x.toString())
				.collect(Collectors.joining(", "));
	}
}*/
