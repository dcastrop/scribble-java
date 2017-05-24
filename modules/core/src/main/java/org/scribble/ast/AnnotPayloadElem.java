package org.scribble.ast;

import org.antlr.runtime.tree.CommonTree;
import org.scribble.ast.name.qualified.DataTypeNode;
import org.scribble.ast.name.simple.VarNameNode;
import org.scribble.del.ScribDel;
import org.scribble.main.ScribbleException;
import org.scribble.sesstype.AnnotPayload;
import org.scribble.sesstype.kind.PayloadTypeKind;
import org.scribble.util.ScribUtil;
import org.scribble.visit.AstVisitor;

// Cf. DoArg, wrapper for a (unary) name node of potentially unknown kind (needs disamb)
// PayloadTypeKind is DataType or Local, but Local has its own special subclass (and protocol params not allowed), so this should implicitly be for DataType only
// AST hierarchy requires unary and delegation (binary pair) payloads to be structurally distinguished
//public class DataTypeElem extends PayloadElem<DataTypeKind>
public class AnnotPayloadElem<K extends PayloadTypeKind> extends ScribNodeBase implements PayloadElem<K>//extends PayloadElem
{
	//public final PayloadElemNameNode<DataTypeKind> name;
	//public final DataTypeNode data; 
	public final VarNameNode varName;   // (Ambig.) DataTypeNode or parameter
	public final DataTypeNode dataType;
	
	//public DataTypeElem(PayloadElemNameNode<DataTypeKind> name)
	//public UnaryPayloadlem(DataTypeNode data)
	//public UnaryPayloadElem(PayloadElemNameNode name)
	public AnnotPayloadElem(CommonTree source, VarNameNode varname, DataTypeNode dataType)
	{
		//super(name);
		//this.data = data;
		super(source);
		this.varName = varname;
		this.dataType = dataType; 
	}
	
	@Override
	public AnnotPayloadElem<K> project()
	{
		return this;
	}

	@Override
	protected AnnotPayloadElem<K> copy()
	{
		//return new UnaryPayloadElem(this.data);
		return new AnnotPayloadElem<>(this.source, this.varName, this.dataType);
	}
	
	@Override
	public AnnotPayloadElem<K> clone()
	{
		//PayloadElemNameNode<DataTypeKind> name = (PayloadElemNameNode<DataTypeKind>) this.data.clone();  // FIXME: make a DataTypeNameNode
		//PayloadElemNameNode<K> name = (PayloadElemNameNode<K>) this.name.clone();
		VarNameNode varname = ScribUtil.checkNodeClassEquality(this.varName, this.varName.clone());
		DataTypeNode datatype = ScribUtil.checkNodeClassEquality(this.dataType, this.dataType.clone());
		return AstFactoryImpl.FACTORY.AnnotPayloadElem(this.source, varname, datatype);
	}

	//public DataTypeElem reconstruct(PayloadElemNameNode<DataTypeKind> name)
	//public UnaryPayloadElem reconstruct(DataTypeNode name)
	public AnnotPayloadElem<K> reconstruct(VarNameNode name, DataTypeNode dataType)
	{
		ScribDel del = del();
		AnnotPayloadElem<K> elem = new AnnotPayloadElem<>(this.source, name, dataType);
		elem = ScribNodeBase.del(elem, del);
		return elem;
	}

	@Override 
	public AnnotPayloadElem<K> visitChildren(AstVisitor nv) throws ScribbleException
	{
		//PayloadElemNameNode<DataTypeKind> name = (PayloadElemNameNode<DataTypeKind>) visitChild(this.data, nv);
		//DataTypeNode name = (PayloadElemNameNode<DataTypeKind>) visitChild(this.data, nv);
		VarNameNode varName = (VarNameNode) visitChild(this.varName, nv);  
		DataTypeNode dataType = (DataTypeNode) visitChild(this.dataType, nv);
				// FIXME: probably need to record an explicit kind token, for "cast checking"
				// Cannot use ScribNodeBase.visitChildWithCastCheck because this is not a ProtocolKindNode
		//PayloadElemNameNode<K> name = (PayloadElemNameNode<K>) visitChildWithClassEqualityCheck(this, this.name, nv);  // No: can be initially Ambig
		return reconstruct(varName, dataType);
	}
	
	@Override
	public String toString()
	{
		//return this.data.toString();
		return this.varName.toString() + ' ' +  this.dataType.toString();
	}

	@Override
	//public PayloadType<DataTypeKind> toPayloadType()  // Currently can assume the only possible kind is DataTypeKind
	//public PayloadType<? extends PayloadTypeKind> toPayloadType()  // Currently can assume the only possible kind is DataTypeKind
	public AnnotPayload toPayloadType()  // Currently can assume the only possible kind is DataTypeKind
	{
		// TODO: make it PayloadType AnnotPayload 
		return new AnnotPayload(this.varName.toPayloadType(), this.dataType.toPayloadType());
	}
}