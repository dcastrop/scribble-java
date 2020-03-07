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
package org.scribble.ext.assrt.parser.assertions;

import org.antlr.runtime.Token;
import org.antlr.runtime.tree.CommonTreeAdaptor;
import org.scribble.ext.assrt.ast.AssrtLocatedStateVarDeclList;
import org.scribble.ext.assrt.ast.AssrtStateVarArgList;
import org.scribble.ext.assrt.ast.AssrtStateVarDecl;
import org.scribble.ext.assrt.ast.AssrtStateVarDeclList;
import org.scribble.ext.assrt.ast.AssrtStateVarHeaderAnnot;

// Cf. ScribTreeAdaptor
public class AssertionsTreeAdaptor extends CommonTreeAdaptor
{
	public AssertionsTreeAdaptor()
	{
		super();
	}

	@Override
	public Object create(Token t)
	{
		if (t == null)  // Cf. ScribNil?
		{
			return super.create(t);
		}

		switch (t.getText())
		{
		case "ASSRT_HEADERANNOT":
			return new AssrtStateVarHeaderAnnot(t);
		case "ASSRT_STATEVARDECL_LIST":
			return new AssrtStateVarDeclList(t);
		case "ASSRT_STATEVARDECL":
			return new AssrtStateVarDecl(t);
		case "ASSRT_STATEVARARG_LIST":
			return new AssrtStateVarArgList(t);

		case "ASSRT_LOCATEDSTATEVARDECLLIST":
			return new AssrtLocatedStateVarDeclList(t);

		default:
			return super.create(t);
		}
	}
}
