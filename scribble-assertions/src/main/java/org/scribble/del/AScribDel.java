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
package org.scribble.del;

import org.scribble.ast.ScribNode;
import org.scribble.main.ScribbleException;
import org.scribble.visit.wf.AAnnotationChecker;

public interface AScribDel extends ScribDel
{
	default void enterAnnotCheck(ScribNode parent, ScribNode child, AAnnotationChecker checker) throws ScribbleException
	{
		 
	}
	
	default ScribNode leaveAnnotCheck(ScribNode parent, ScribNode child,  AAnnotationChecker checker, ScribNode visited) throws ScribbleException
	{
		return visited;
	}
}
