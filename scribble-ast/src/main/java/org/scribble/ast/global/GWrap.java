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
package org.scribble.ast.global;

import org.antlr.runtime.Token;
import org.scribble.ast.BasicInteraction;
import org.scribble.ast.name.simple.RoleNode;
import org.scribble.core.type.kind.Global;
import org.scribble.util.Constants;
import org.scribble.util.ScribException;
import org.scribble.visit.AstVisitor;

// TODO: factor out base Wrap (cf. Disconnect)
public class GWrap extends BasicInteraction<Global>
		implements GSimpleSessionNode
{
	public static final int CLIENT_CHILD_INDEX = 0;
	public static final int SERVER_CHILD_INDEX = 1;

	// ScribTreeAdaptor#create constructor
	public GWrap(Token t)
	{
		super(t);
	}

	// Tree#dupNode constructor
	public GWrap(GWrap node)
	{
		super(node);
	}
	
	public RoleNode getClientChild()
	{
		return (RoleNode) getChild(CLIENT_CHILD_INDEX);
	}

	public RoleNode getServerChild()
	{
		return (RoleNode) getChild(SERVER_CHILD_INDEX);
	}

	// "add", not "set"
	public void addChildren1(RoleNode client, RoleNode server)
	{
		// Cf. above getters and Scribble.g children order
		addChild(client);
		addChild(server);
	}
	
	@Override
	public GWrap dupNode()
	{
		return new GWrap(this);
	}

	public GWrap reconstruct(RoleNode client, RoleNode server)
	{
		GWrap n = dupNode();
		n.addChildren1(client, server);
		n.setDel(del());  // No copy
		return n;
	}

	@Override
	public GWrap visitChildren(AstVisitor nv) throws ScribException
	{
		RoleNode src = (RoleNode) visitChild(getClientChild(), nv);
		RoleNode dest = (RoleNode) visitChild(getServerChild(), nv);
		return reconstruct(src, dest);
	}

	@Override
	public String toString()
	{
		return Constants.WRAP_KW + " " + getClientChild()
				+ " " + Constants.TO_KW + " " + getServerChild() + ";";
	}
}