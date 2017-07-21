package org.scribble.ext.assrt.del.global;

import org.scribble.ast.ConnectionAction;
import org.scribble.ast.MessageSigNode;
import org.scribble.ast.PayloadElem;
import org.scribble.ast.ScribNode;
import org.scribble.del.global.GConnectDel;
import org.scribble.ext.assrt.del.AssrtScribDel;
import org.scribble.ext.assrt.sesstype.name.AssrtAnnotDataType;
import org.scribble.ext.assrt.sesstype.name.AssrtDataTypeVar;
import org.scribble.ext.assrt.sesstype.name.AssrtPayloadElemType;
import org.scribble.ext.assrt.visit.wf.AssrtAnnotationChecker;
import org.scribble.ext.assrt.visit.wf.env.AssrtAnnotationEnv;
import org.scribble.main.ScribbleException;
import org.scribble.sesstype.name.PayloadElemType;
import org.scribble.sesstype.name.Role;

public class AssrtGConnectDel extends GConnectDel implements AssrtScribDel
{
	public AssrtGConnectDel()
	{
		
	}

	// Duplicated from AssrtGMessageTransferDel
	@Override
	public ConnectionAction<?> leaveAnnotCheck(ScribNode parent, ScribNode child, AssrtAnnotationChecker checker, ScribNode visited) throws ScribbleException
	{
		ConnectionAction<?> ca = (ConnectionAction<?>) visited;
		AssrtAnnotationEnv env = checker.popEnv();

		if (ca.msg.isMessageSigNode())
		{	
			Role src = ca.src.toName();
			Role dest = ca.dest.toName();   
			
			for (PayloadElem<?> pe : ((MessageSigNode) ca.msg).payloads.getElements())
			{
				PayloadElemType<?> peType = pe.toPayloadType(); 
				if (peType instanceof AssrtPayloadElemType<?>)
				{
					AssrtPayloadElemType<?> apt = (AssrtPayloadElemType<?>) peType;
					if (apt.isAnnotVarDecl())
					{
						AssrtAnnotDataType adt = (AssrtAnnotDataType) apt;
						if (env.isDataTypeVarBound(adt.var))
						{
							throw new ScribbleException("Payload var " + pe + " is already declared."); 
						}
						env = env.addAnnotDataType(src, adt); 
						env = env.addDataTypeVarName(dest, adt.var);
					}
					else //if (apt.isAnnotVarName())
					{
						AssrtDataTypeVar v = (AssrtDataTypeVar) apt;
						if (!env.isDataTypeVarKnown(src, v))
						{
							throw new ScribbleException("Payload var " + pe + " is not in scope for role: " + src);
						}
						env = env.addDataTypeVarName(dest, v);
					}
				}
			}
		}
		else
		{
			throw new RuntimeException("[scrib-assert] TODO: " + ca.msg);
		}
		
		checker.pushEnv(env);
		return ca; 
	}
}