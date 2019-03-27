package org.scribble.ext.assrt.type.formula;

import org.sosy_lab.java_smt.api.BooleanFormula;

// Binary boolean -- top-level formula of assertions
// N.B. equals/hashCode is only for "syntactic" comparison
public abstract class AssrtBoolFormula extends AssrtSmtFormula<BooleanFormula>
{
	public AssrtBoolFormula()
	{

	}
	
	@Override
	public abstract AssrtBoolFormula squash();

	@Override
	public abstract AssrtBoolFormula subs(AssrtIntVarFormula old, AssrtIntVarFormula neu);
	
	public abstract AssrtBoolFormula getCnf();
	@Deprecated
	public abstract boolean isNF(AssrtBinBoolFormula.Op top);
	public abstract boolean hasOp(AssrtBinBoolFormula.Op op);
}