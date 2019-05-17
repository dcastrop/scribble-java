package org.scribble.ext.assrt.ast.local;

import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import org.antlr.runtime.Token;
import org.scribble.ast.NonRoleParamDeclList;
import org.scribble.ast.RoleDeclList;
import org.scribble.ast.ScribNode;
import org.scribble.ast.local.LProtoHeader;
import org.scribble.ast.name.qualified.ProtoNameNode;
import org.scribble.core.type.kind.Local;
import org.scribble.del.DelFactory;
import org.scribble.ext.assrt.ast.AssrtArithExpr;
import org.scribble.ext.assrt.ast.AssrtAssertion;
import org.scribble.ext.assrt.ast.AssrtStateVarDeclAnnotNode;
import org.scribble.ext.assrt.ast.name.simple.AssrtIntVarNameNode;
import org.scribble.ext.assrt.core.type.formula.AssrtArithFormula;
import org.scribble.ext.assrt.core.type.name.AssrtDataTypeVar;
import org.scribble.ext.assrt.del.AssrtDelFactory;
import org.scribble.util.ScribException;
import org.scribble.visit.AstVisitor;

// Based on AssrtGProtocolHeader
public class AssrtLProtoHeader extends LProtoHeader
		implements AssrtStateVarDeclAnnotNode
{
	//public static final int ROLEDECLLIST_CHILD = 2;
	// FIXME: no: Assertions.g gives back a subtree containing all
	public static final int ASSERT_CHILD_INDEX = 3;  // May be null (means "true")
	public static final int ANNOT_CHILDREN_START_INDEX = 4;

	// ScribTreeAdaptor#create constructor
	public AssrtLProtoHeader(Token t)
	{
		super(t);
	}
	
	// Tree#dupNode constructor
	protected AssrtLProtoHeader(AssrtLProtoHeader node)
	{
		super(node);
	}
	
	// CHECKME: define restrictions directly in ANTLR grammar, and make a separate AST class for protocol header var init-decl annotations
	// Pre: ass != null
	//public AssrtBinCompFormula getAnnotDataTypeVarInitDecl()  // Cf. AssrtAnnotDataTypeElem (no "initializer")
	public Map<AssrtDataTypeVar, AssrtArithFormula> getAnnotDataTypeVarDecls()  // Cf. AssrtAnnotDataTypeElem (no "initializer")
	{
		//return (this.ass == null) ? null : (AssrtBinCompFormula) this.ass.getFormula();
		//return (AssrtBinCompFormula) this.ass.getFormula();
		Iterator<AssrtArithExpr> exprs = getAnnotExprChildren().iterator();
		return getAnnotVarChildren().stream().collect(
				Collectors.toMap(v -> v.toName(), v -> exprs.next().getFormula()));
	}

	// N.B. null if not specified -- currently duplicated from AssrtGMessageTransfer
	@Override
	public AssrtAssertion getAssertionChild()
	{
		return (AssrtAssertion) getChild(ASSERT_CHILD_INDEX);
	}
	
	@Override
	public List<AssrtIntVarNameNode> getAnnotVarChildren()
	{
		List<? extends ScribNode> cs = getChildren();
		return cs.subList(ANNOT_CHILDREN_START_INDEX, cs.size()).stream()  // TODO: refactor, cf. Module::getMemberChildren
				.filter(x -> x instanceof AssrtIntVarNameNode)
				.map(x -> (AssrtIntVarNameNode) x).collect(Collectors.toList());
	}

	@Override
	public List<AssrtArithExpr> getAnnotExprChildren()
	{
		List<? extends ScribNode> cs = getChildren();
		return cs.subList(ANNOT_CHILDREN_START_INDEX, cs.size()).stream()  // TODO: refactor, cf. Module::getMemberChildren
				.filter(x -> x instanceof AssrtArithExpr)
				.map(x -> (AssrtArithExpr) x).collect(Collectors.toList());
	}

	@Override
	public void addScribChildren(ProtoNameNode<Local> name,
			NonRoleParamDeclList ps, RoleDeclList rs)
	{
		throw new RuntimeException("Deprecated for " + getClass() + ":\n\t" + this);
	}

	// "add", not "set"
	public void addScribChildren(ProtoNameNode<Local> name,
			NonRoleParamDeclList ps, RoleDeclList rs, AssrtAssertion assrt,
			List<AssrtIntVarNameNode> avars, List<AssrtArithExpr> aexprs)
	{
		// Cf. above getters and Scribble.g children order
		super.addScribChildren(name, ps, rs);
		addChild(assrt);
		addChildren(avars);
		addChildren(aexprs);
	}
	
	@Override
	public AssrtLProtoHeader dupNode()
	{
		return new AssrtLProtoHeader(this);
	}
	
	@Override
	public void decorateDel(DelFactory df)
	{
		((AssrtDelFactory) df).AssrtLProtoHeader(this);
	}

	@Override
	public AssrtLProtoHeader reconstruct(ProtoNameNode<Local> name,
			NonRoleParamDeclList ps, RoleDeclList rs)
	{
		throw new RuntimeException(
				"[assrt] Deprecated for " + getClass() + ":\n\t" + this);
	}

	public AssrtLProtoHeader reconstruct(ProtoNameNode<Local> name,
			NonRoleParamDeclList ps, RoleDeclList rs, AssrtAssertion ass,
			List<AssrtIntVarNameNode> avars, List<AssrtArithExpr> aexprs)
	{
		AssrtLProtoHeader dup = dupNode();
		dup.addScribChildren(name, ps, rs, ass, avars, aexprs);
		dup.setDel(del());  // No copy
		return dup;
	}
	
	@Override
	public LProtoHeader visitChildren(AstVisitor v) throws ScribException
	{
		/*ProtocolNameNode<K> nameNodeChild = (ProtocolNameNode<K>) visitChild(
				getNameNodeChild(), nv);*/  // Don't really need to visit, and can avoid generic cast
		RoleDeclList rs = (RoleDeclList) visitChild(getRoleDeclListChild(), v);
		NonRoleParamDeclList ps = (NonRoleParamDeclList) 
				visitChild(getParamDeclListChild(), v);
		List<AssrtIntVarNameNode> annotvars = visitChildListWithClassEqualityCheck(
				this, getAnnotVarChildren(), v);
		List<AssrtArithExpr> aexprs = visitChildListWithClassEqualityCheck(this,
				getAnnotExprChildren(), v);
		AssrtAssertion tmp = getAssertionChild();
		AssrtAssertion ass = (tmp == null) 
				? null
				: (AssrtAssertion) visitChild(tmp, v);
		return reconstruct(getNameNodeChild(), ps, rs, ass, annotvars, aexprs);
	}
	
	@Override
	public String toString()
	{
		return super.toString() //+ " " + this.ass;
				+ annotToString();
	}
}

















/*
	public final List<AssrtIntVarNameNode> annotvars;
	public final List<AssrtArithExpr> annotexprs;
	public final AssrtAssertion ass;  // null if not specified -- currently duplicated from AssrtGMessageTransfer

	public AssrtLProtoHeader(CommonTree source, LProtocolNameNode name, RoleDeclList roledecls, NonRoleParamDeclList paramdecls)
	{
		this(source, name, roledecls, paramdecls, //null);
				Collections.emptyList(), Collections.emptyList(),
				null);
	}

	public AssrtLProtoHeader(CommonTree source, LProtocolNameNode name, RoleDeclList roledecls, NonRoleParamDeclList paramdecls, //AssrtAssertion ass)
			List<AssrtIntVarNameNode> annotvars, List<AssrtArithExpr> annotexprs,
			AssrtAssertion ass)
	{
		super(source, name, roledecls, paramdecls);
		this.annotvars = Collections.unmodifiableList(annotvars);
		this.annotexprs = Collections.unmodifiableList(annotexprs);
		this.ass = ass;
	}
//*/
	