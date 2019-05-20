package org.scribble.ext.assrt.core.model.endpoint;

import java.util.List;
import java.util.Map;
import java.util.Set;

import org.scribble.core.type.name.MsgId;
import org.scribble.core.type.name.RecVar;
import org.scribble.core.type.name.Role;
import org.scribble.core.type.session.Payload;
import org.scribble.ext.assrt.core.model.endpoint.action.AssrtCoreEAcc;
import org.scribble.ext.assrt.core.model.endpoint.action.AssrtCoreERecv;
import org.scribble.ext.assrt.core.model.endpoint.action.AssrtCoreEReq;
import org.scribble.ext.assrt.core.model.endpoint.action.AssrtCoreESend;
import org.scribble.ext.assrt.core.model.stp.AssrtStpEState;
import org.scribble.ext.assrt.core.model.stp.action.AssrtStpEReceive;
import org.scribble.ext.assrt.core.model.stp.action.AssrtStpESend;
import org.scribble.ext.assrt.core.type.formula.AssrtAFormula;
import org.scribble.ext.assrt.core.type.formula.AssrtBFormula;
import org.scribble.ext.assrt.core.type.formula.AssrtIntVarFormula;
import org.scribble.ext.assrt.core.type.formula.AssrtSmtFormula;
import org.scribble.ext.assrt.model.endpoint.AssrtEModelFactory;

public interface AssrtCoreEModelFactory extends AssrtEModelFactory
{

	AssrtCoreESend newAssrtCoreESend(Role peer, MsgId<?> mid, Payload payload,
			AssrtBFormula bf, List<AssrtAFormula> stateexprs);
	AssrtCoreERecv newAssrtCoreEReceive(Role peer, MsgId<?> mid,
			Payload payload, AssrtBFormula bf, List<AssrtAFormula> stateexprs);
	AssrtCoreEReq newAssrtCoreERequest(Role peer, MsgId<?> mid,
			Payload payload, AssrtBFormula bf, List<AssrtAFormula> stateexprs);
	AssrtCoreEAcc newAssrtCoreEAccept(Role peer, MsgId<?> mid, Payload payload,
			AssrtBFormula bf, List<AssrtAFormula> stateexprs);

	AssrtStpEState newAssertStpEState(Set<RecVar> labs);
	
	AssrtStpESend newAssrtStpESend(Role peer, MsgId<?> mid, Payload payload, 
			Map<AssrtIntVarFormula, AssrtSmtFormula<?>> sigma, AssrtBFormula A);
	AssrtStpEReceive newAssrtStpEReceive(Role peer, MsgId<?> mid, Payload payload,
			Map<AssrtIntVarFormula, AssrtSmtFormula<?>> sigma, AssrtBFormula A);
}
