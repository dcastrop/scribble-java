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

import org.scribble.ast.AstFactoryImpl;
import org.scribble.ast.AuxMod;
import org.scribble.ast.DataDecl;
import org.scribble.ast.DataParamDecl;
import org.scribble.ast.ExplicitMod;
import org.scribble.ast.ImportModule;
import org.scribble.ast.Module;
import org.scribble.ast.ModuleDecl;
import org.scribble.ast.NonRoleArg;
import org.scribble.ast.NonRoleArgList;
import org.scribble.ast.NonRoleParamDeclList;
import org.scribble.ast.PayElemList;
import org.scribble.ast.ProtoModList;
import org.scribble.ast.RoleArg;
import org.scribble.ast.RoleArgList;
import org.scribble.ast.RoleDecl;
import org.scribble.ast.RoleDeclList;
import org.scribble.ast.ScribNodeBase;
import org.scribble.ast.SigDecl;
import org.scribble.ast.SigLitNode;
import org.scribble.ast.SigParamDecl;
import org.scribble.ast.UnaryPayElem;
import org.scribble.ast.global.GChoice;
import org.scribble.ast.global.GConnect;
import org.scribble.ast.global.GContinue;
import org.scribble.ast.global.GDelegPayElem;
import org.scribble.ast.global.GDisconnect;
import org.scribble.ast.global.GDo;
import org.scribble.ast.global.GInteractionSeq;
import org.scribble.ast.global.GMsgTransfer;
import org.scribble.ast.global.GProtoBlock;
import org.scribble.ast.global.GProtoDecl;
import org.scribble.ast.global.GProtoDef;
import org.scribble.ast.global.GProtoHeader;
import org.scribble.ast.global.GRecursion;
import org.scribble.ast.global.GWrap;
import org.scribble.ast.name.qualified.DataNameNode;
import org.scribble.ast.name.qualified.GProtoNameNode;
import org.scribble.ast.name.qualified.LProtoNameNode;
import org.scribble.ast.name.qualified.ModuleNameNode;
import org.scribble.ast.name.qualified.SigNameNode;
import org.scribble.ast.name.simple.AmbigNameNode;
import org.scribble.ast.name.simple.DataParamNode;
import org.scribble.ast.name.simple.ExtIdNode;
import org.scribble.ast.name.simple.IdNode;
import org.scribble.ast.name.simple.OpNode;
import org.scribble.ast.name.simple.RecVarNode;
import org.scribble.ast.name.simple.RoleNode;
import org.scribble.ast.name.simple.SigParamNode;
import org.scribble.del.global.GChoiceDel;
import org.scribble.del.global.GConnectDel;
import org.scribble.del.global.GContinueDel;
import org.scribble.del.global.GDelegationElemDel;
import org.scribble.del.global.GDisconnectDel;
import org.scribble.del.global.GDoDel;
import org.scribble.del.global.GInteractionSeqDel;
import org.scribble.del.global.GMessageTransferDel;
import org.scribble.del.global.GProtoBlockDel;
import org.scribble.del.global.GProtoDeclDel;
import org.scribble.del.global.GProtoDefDel;
import org.scribble.del.global.GRecursionDel;
import org.scribble.del.global.GWrapDel;
import org.scribble.del.name.qualified.DataNameNodeDel;
import org.scribble.del.name.qualified.SigNameNodeDel;
import org.scribble.del.name.simple.AmbigNameNodeDel;
import org.scribble.del.name.simple.NonRoleParamNodeDel;
import org.scribble.del.name.simple.RecVarNodeDel;
import org.scribble.del.name.simple.RoleNodeDel;


//CHECKME: refactor decoration methods into AST interface, to ensure they are implemented and called?
//CHECKME: to what extent are del's still needed?
public class DelFactoryImpl implements DelFactory
{
	public DelFactoryImpl()
	{
		
	}

	protected ScribDel createDefaultDel()
	{
		return new DefaultDel();
	}
	
	// Mutating setter
	protected static void setDel(ScribNodeBase n, ScribDel del)
	{
		AstFactoryImpl.setDel(n, del);
	}

	@Override
	public void IdNode(IdNode n)
	{
		setDel(n, createDefaultDel());  // Necessary?
	}

	@Override
	public void ExtIdNode(ExtIdNode n)
	{
		setDel(n, createDefaultDel());  // Necessary?
	}

	@Override
	public void AmbigNameNode(AmbigNameNode n)
	{
		setDel(n, new AmbigNameNodeDel());
	}

	@Override
	public void DataParamNode(DataParamNode n)
	{
		setDel(n, new NonRoleParamNodeDel());
	}

	@Override
	public void OpNode(OpNode n)
	{
		setDel(n, createDefaultDel());
	}

	@Override
	public void RecVarNode(RecVarNode n)
	{
		setDel(n, new RecVarNodeDel());
	}

	@Override
	public void RoleNode(RoleNode r)
	{
		setDel(r, new RoleNodeDel());
	}

	@Override
	public void SigParamNode(SigParamNode n)
	{
		setDel(n, new NonRoleParamNodeDel());
	}

	@Override
	public void DataNameNode(DataNameNode n)
	{
		setDel(n, new DataNameNodeDel());
	}

	@Override
	public void GProtoNameNode(GProtoNameNode n)
	{
		setDel(n, createDefaultDel());
	}

	@Override
	public void LProtoNameNode(LProtoNameNode n)
	{
		setDel(n, createDefaultDel());
	}

	@Override
	public void ModuleNameNode(ModuleNameNode n)
	{
		setDel(n, createDefaultDel());
	}

	@Override
	public void SigNameNode(SigNameNode n)
	{
		setDel(n, new SigNameNodeDel());
	}
	
	@Override
	public void Module(Module n)
	{
		setDel(n, new ModuleDel());
	}

	@Override
	public void ModuleDecl(ModuleDecl n)
	{
		setDel(n, createDefaultDel());
	}

	@Override
	public void ImportModule(ImportModule n)
	{
		setDel(n, new ImportModuleDel());
	}

	@Override
	public void DataDecl(DataDecl n)
	{
		setDel(n, createDefaultDel());
	}
	
	@Override
	public void SigDecl(SigDecl n)
	{
		setDel(n, createDefaultDel());
	}

	@Override
	public void GProtoDecl(GProtoDecl n)
	{
		setDel(n, new GProtoDeclDel());
	}

	@Override
	public void ProtoModList(ProtoModList n)
	{
		setDel(n, createDefaultDel());
	}

	@Override
	public void AuxMod(AuxMod n)
	{
		setDel(n, createDefaultDel());
	}

	@Override
	public void ExplicitMod(ExplicitMod n)
	{
		setDel(n, createDefaultDel());
	}

	@Override
	public void GProtoHeader(GProtoHeader n)
	{
		setDel(n, createDefaultDel());
	}

	@Override
	public void RoleDeclList(RoleDeclList n)
	{
		setDel(n, new RoleDeclListDel());
	}

	@Override
	public void RoleDecl(RoleDecl n)
	{
		setDel(n, new RoleDeclDel());
	}

	@Override
	public void NonRoleParamDeclList(NonRoleParamDeclList n)
	{
		setDel(n, new NonRoleParamDeclListDel());
	}

	@Override
	public void DataParamDecl(DataParamDecl n)
	{
		setDel(n, new NonRoleParamDeclDel());
	}

	@Override
	public void SigParamDecl(SigParamDecl sd)
	{
		setDel(sd, new NonRoleParamDeclDel());
	}

	@Override
	public void GProtoDef(GProtoDef n)
	{
		setDel(n, new GProtoDefDel());
	}

	@Override
	public void GProtoBlock(GProtoBlock n)
	{
		setDel(n, new GProtoBlockDel());
	}

	@Override
	public void GInteractionSeq(GInteractionSeq n)
	{
		setDel(n, new GInteractionSeqDel());
	}

	@Override
	public void SigLitNode(SigLitNode n)
	{
		setDel(n, createDefaultDel());
	}

	@Override
	public void PayElemList(PayElemList n)
	{
		setDel(n, createDefaultDel());
		//setDel(pay, new PayloadElemListDel());
	}

	@Override
	public void UnaryPayElem(UnaryPayElem<?> n)
	{
		setDel(n, createDefaultDel());
	}

	@Override
	public void GDelegPayElem(GDelegPayElem n)
	{
		//setDel(n, createDefaultDelegate());
		setDel(n, new GDelegationElemDel());
	}

	/*@Override
	public LDelegationElem LDelegationElem(CommonTree source, LProtocolNameNode proto)
	{
		LDelegationElem de = new LDelegationElem(source, proto);
		de = setDel(de, createDefaultDelegate());
		return de;
	}*/

	@Override
	public void GConnect(GConnect n)
	{
		setDel(n, new GConnectDel());
	}

	@Override
	public void GDisconnect(GDisconnect n)
	{
		setDel(n, new GDisconnectDel());
	}

	@Override
	public void GMsgTransfer(GMsgTransfer n)
	{
		setDel(n, new GMessageTransferDel());
	}

	@Override
	public void GWrap(GWrap n)
	{
		setDel(n, new GWrapDel());
	}

	@Override
	public void GContinue(GContinue n)
	{
		setDel(n, new GContinueDel());
	}

	@Override
	public void GDo(GDo n)
	{
		setDel(n, new GDoDel());
	}

	@Override
	public void RoleArgList(RoleArgList n)
	{
		setDel(n, new RoleArgListDel());
	}

	@Override
	public void RoleArg(RoleArg n)
	{
		setDel(n, createDefaultDel());
	}

	@Override
	public void NonRoleArgList(NonRoleArgList n)
	{
		setDel(n, new NonRoleArgListDel());
	}

	@Override
	public void NonRoleArg(NonRoleArg n)
	{
		setDel(n, createDefaultDel());
	}

	@Override
	public void GChoice(GChoice n)
	{
		setDel(n, new GChoiceDel());
	}

	@Override
	public void GRecursion(GRecursion n)
	{
		setDel(n, new GRecursionDel());
	}
}

	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	/*@Override
	public DummyProjectionRoleNode DummyProjectionRoleNode()
	{
		DummyProjectionRoleNode dprn = new DummyProjectionRoleNode();
		dprn = (DummyProjectionRoleNode) dprn.del(createDefaultDelegate());
		return dprn;
	}*/

	/*@Override  // Called from LProtocolDecl::clone, but currently never used  -- local proto decls only projected, not parsed
	public LProtocolDecl LProtocolDecl(CommonTree source, List<ProtocolDecl.Modifiers> mods, LProtocolHeader header, LProtocolDef def)
	{
		LProtocolDecl lpd = new LProtocolDecl(source, mods, header, def);
		lpd = setDel(lpd, new LProtocolDeclDel());
		return lpd;
	}

	@Override
	public LProjectionDecl LProjectionDecl(CommonTree source, List<ProtocolDecl.Modifiers> mods, GProtocolName fullname, Role self, LProtocolHeader header, LProtocolDef def)  // del extends that of LProtocolDecl 
	{
		LProjectionDecl lpd = new LProjectionDecl(source, mods, header, def);
		lpd = ScribNodeBase.setDel(lpd, new LProjectionDeclDel(fullname, self));
		return lpd;
	}

	@Override
	public LProtocolHeader LProtocolHeader(CommonTree source, LProtocolNameNode name, RoleDeclList roledecls, NonRoleParamDeclList paramdecls)
	{
		LProtocolHeader lph = new LProtocolHeader(source, name, roledecls, paramdecls);
		lph = setDel(lph, createDefaultDelegate());
		return lph;
	}

	@Override
	public SelfRoleDecl SelfRoleDecl(CommonTree source, RoleNode namenode)
	{
		SelfRoleDecl rd = new SelfRoleDecl(source, namenode);
		rd = setDel(rd, new RoleDeclDel());
		return rd;
	}

	@Override
	public LProtocolDef LProtocolDef(CommonTree source, LProtocolBlock block)
	{
		LProtocolDef lpd = new LProtocolDef(source, block);
		lpd = setDel(lpd, new LProtocolDefDel());
		return lpd;
	}

	@Override
	public LProtocolBlock LProtocolBlock(CommonTree source, LInteractionSeq seq)
	{
		LProtocolBlock lpb = new LProtocolBlock(source, seq);
		lpb = setDel(lpb, new LProtocolBlockDel());
		return lpb;
	}

	@Override
	public LInteractionSeq LInteractionSeq(CommonTree source, List<LInteractionNode> actions)
	{
		LInteractionSeq lis = new LInteractionSeq(source, actions);
		lis = setDel(lis, new LInteractionSeqDel());
		return lis;
	}

	@Override
	public LSend LSend(CommonTree source, RoleNode src, MessageNode msg, List<RoleNode> dests)
	{
		LSend ls = new LSend(source, src, msg, dests);
		ls = setDel(ls, new LSendDel());
		return ls;
	}

	@Override
	public LReceive LReceive(CommonTree source, RoleNode src, MessageNode msg, List<RoleNode> dests)
	{
		LReceive ls = new LReceive(source, src, msg, dests);
		ls = setDel(ls, new LReceiveDel());
		return ls;
	}
	
	@Override
	public LRequest LRequest(CommonTree source, RoleNode src, MessageNode msg, RoleNode dest)
	//public LConnect LConnect(RoleNode src, RoleNode dest)
	{
		LRequest lc = new LRequest(source, src, msg, dest);
		//LConnect lc = new LConnect(src, dest);
		lc = setDel(lc, new LRequestDel());
		return lc;
	}

	@Override
	public LAccept LAccept(CommonTree source, RoleNode src, MessageNode msg, RoleNode dest)
	//public LAccept LAccept(RoleNode src, RoleNode dest)
	{
		LAccept la = new LAccept(source, src, msg, dest);
		//LAccept la = new LAccept(src, dest);
		la = setDel(la, new LAcceptDel());
		return la;
	}

	@Override
	public LDisconnect LDisconnect(CommonTree source, RoleNode self, RoleNode peer)
	{
		LDisconnect lc = new LDisconnect(source, UnitMessageSigNode(), self, peer);
		lc = setDel(lc, new LDisconnectDel());
		return lc;
	}

	@Override
	public LWrapClient LWrapClient(CommonTree source, RoleNode self, RoleNode peer)
	{
		LWrapClient lwc = new LWrapClient(source, UnitMessageSigNode(), self, peer);
		lwc = setDel(lwc, new LWrapClientDel());
		return lwc;
	}

	@Override
	public LWrapServer LWrapServer(CommonTree source, RoleNode self, RoleNode peer)
	{
		LWrapServer lws = new LWrapServer(source, UnitMessageSigNode(), self, peer);
		lws = setDel(lws, new LWrapServerDel());
		return lws;
	}

	@Override
	public LChoice LChoice(CommonTree source, RoleNode subj, List<LProtocolBlock> blocks)
	{
		LChoice lc = new LChoice(source, subj, blocks);
		lc = setDel(lc, new LChoiceDel());
		return lc;
	}

	@Override
	public LRecursion LRecursion(CommonTree source, RecVarNode recvar, LProtocolBlock block)
	{
		LRecursion lr = new LRecursion(source, recvar, block);
		lr = setDel(lr, new LRecursionDel());
		return lr;
	}

	@Override
	public LContinue LContinue(CommonTree source, RecVarNode recvar)
	{
		LContinue lc = new LContinue(source, recvar);
		lc = setDel(lc, new LContinueDel());
		return lc;
	}

	@Override
	public LDo LDo(CommonTree source, RoleArgList roleinstans, NonRoleArgList arginstans, LProtocolNameNode proto)
	{
		LDo ld = new LDo(source, roleinstans, arginstans, proto);
		ld = setDel(ld, new LDoDel());
		return ld;
	}*/