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
package org.scribble.parser;

import java.io.IOException;
import java.io.InputStream;
import java.util.List;
import java.util.stream.Collectors;

import org.antlr.runtime.ANTLRStringStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.Lexer;
import org.antlr.runtime.Parser;
import org.antlr.runtime.RecognitionException;
import org.antlr.runtime.tree.CommonErrorNode;
import org.antlr.runtime.tree.CommonTree;
import org.scribble.ast.Module;
import org.scribble.del.DelFactory;
import org.scribble.parser.antlr.ScribbleLexer;
import org.scribble.parser.antlr.ScribbleParser;
import org.scribble.util.ScribParserException;

// InputStream -> ANTLR CommonTree -- parses Resource.getInputStream() into ANTLR CommonTrees
// Wraps the ScribbleLexer and ScribbleParser generated by ANTLR from Scribble.g
public class ScribAntlrWrapper
{
	public final DelFactory df;  // Will be shared with af and Job (by Main)
	
	public ScribAntlrWrapper(DelFactory df)
	{
		this.df = df;
	}
	
	// Scribble extensions should override newScribbleLexer/Parser as appropriate
	// A fresh Lexer/Parser is needed by each call to parse 
	public Lexer newScribbleLexer(ANTLRStringStream ss)
	{
		return new ScribbleLexer(ss);
	}

	// Scribble extensions should override newScribbleLexer/Parser as appropriate
	// ScribbleParser: a Parser that has a top-level "module" method
	// (And has "setTreeAdaptor")
	public Parser newScribbleParser(CommonTokenStream ts)
	{
		return new ScribbleParser(ts);
	}

	// Parse InputStream (from a Resource) into a Module -- N.B. not del decorated (yet)
	public Module parse(InputStream is) throws ScribParserException
	{
		try
		{
			String input = ScribAntlrWrapper.readInput(is);
			Lexer lex = newScribbleLexer(new ANTLRStringStream(input));
			Module mod = runScribbleParser(new CommonTokenStream(lex));
			return mod;
		}
		catch (IOException e)
		{
			throw new ScribParserException(e);
		}
	}

	protected Module runScribbleParser(CommonTokenStream ts)
			throws ScribParserException
	{
		try
		{
			ScribbleParser p = (ScribbleParser) newScribbleParser(ts);
			
			// FIXME: use reflection, no convenient way to make an interface with module method
			
			p.setTreeAdaptor(new ScribTreeAdaptor(this.df));
			return (Module) p.module().getTree();
					// Cast, because no convenient way to expose an interface for all (Scribble)Parsers with top-level "module" method?
		}
		catch (RecognitionException e)
		{
			throw new ScribParserException(e);
		}
	}

	// CHECKME: should this be used somewhere?
	public static void checkForAntlrErrors(CommonTree t)
	{
		if (t.getChildCount() > 0)  // getChildren returns null instead of empty list 
		{
			List<CommonErrorNode> errors = ((List<?>) t.getChildren()).stream()
					.filter(c -> (c instanceof CommonErrorNode))
					.map(c -> (CommonErrorNode) c)
					.collect(Collectors.toList());
			if (errors.size() > 0)  // Antlr prints errors to System.err by default, but then attempts to carry on
						// Should never get here now, Antlr displayRecognitionError overridden to force exit: Antlr error recovery means not all errors produce CommonErrorNode
			{
				// TODO: improve feedback message
				System.err
						.println("[ScribParser] Aborting due to parsing errors: " + errors);
				System.exit(1);
			}
		}
	}
	
	protected static String readInput(InputStream is) throws IOException
	{
		return new String(ScribAntlrWrapper.readResource(is));
	}

	private static byte[] readResource(InputStream is) throws IOException
	{
		byte[] bs = new byte[is.available()];
		is.read(bs);
		return bs;
	}
}
