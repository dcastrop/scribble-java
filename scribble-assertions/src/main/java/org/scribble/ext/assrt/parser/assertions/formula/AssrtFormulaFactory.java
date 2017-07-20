package org.scribble.ext.assrt.parser.assertions.formula;

import org.antlr.runtime.tree.CommonTree;
import org.scribble.ext.assrt.parser.assertions.AssrtAssertParser;
import org.scribble.ext.assrt.sesstype.formula.AssrtArithFormula;
import org.scribble.ext.assrt.sesstype.formula.AssrtBinArithFormula;
import org.scribble.ext.assrt.sesstype.formula.AssrtBinBoolFormula;
import org.scribble.ext.assrt.sesstype.formula.AssrtBinCompFormula;
import org.scribble.ext.assrt.sesstype.formula.AssrtBoolFormula;
import org.scribble.ext.assrt.sesstype.formula.AssrtIntValFormula;
import org.scribble.ext.assrt.sesstype.formula.AssrtIntVarFormula;


public class AssrtFormulaFactory
{
	public static AssrtBoolFormula parseBoolFormula(
			AssrtAssertParser assertionsScribParser, CommonTree ct) {
		return null;
	}

	public static AssrtIntValFormula parseValue(CommonTree ct, String text) {
		return new AssrtIntValFormula(text);
	}

	public static AssrtIntVarFormula parseVariable(CommonTree ct, String text) {
		return new AssrtIntVarFormula(text);
	}

	public static AssrtBinCompFormula CompFormula(String op, AssrtArithFormula left, AssrtArithFormula right) {
			return new AssrtBinCompFormula(op, left, right); 
	}
	
	public static AssrtBinArithFormula ArithFormula(String op, AssrtArithFormula left, AssrtArithFormula right) {
		return new AssrtBinArithFormula(op, left, right); 
	}
	
	public static AssrtBinBoolFormula BinBoolFormula(String op, AssrtBoolFormula left, AssrtBoolFormula right) {
		return new AssrtBinBoolFormula(op, left, right); 
	}
	
	/*public static AssrtTrueFormula AssrtTrueFormula() 
	{
		return AssrtTrueFormula.TRUE;
	}
	
	public static AssrtFalseFormula AssrtFalseFormula() 
	{ 
	
		return AssrtFalseFormula.FALSE;
	}*/
}
