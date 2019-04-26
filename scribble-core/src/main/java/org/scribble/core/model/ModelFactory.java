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
package org.scribble.core.model;

import java.util.Map;
import java.util.Set;

import org.scribble.core.model.endpoint.EFsm;
import org.scribble.core.model.endpoint.EGraphBuilderUtil;
import org.scribble.core.model.endpoint.EState;
import org.scribble.core.model.endpoint.actions.EAcc;
import org.scribble.core.model.endpoint.actions.EClientWrap;
import org.scribble.core.model.endpoint.actions.EDisconnect;
import org.scribble.core.model.endpoint.actions.ERecv;
import org.scribble.core.model.endpoint.actions.EReq;
import org.scribble.core.model.endpoint.actions.ESend;
import org.scribble.core.model.endpoint.actions.EServerWrap;
import org.scribble.core.model.global.SConfig;
import org.scribble.core.model.global.SGraph;
import org.scribble.core.model.global.SGraphBuilderUtil;
import org.scribble.core.model.global.SModel;
import org.scribble.core.model.global.SingleBuffers;
import org.scribble.core.model.global.SState;
import org.scribble.core.model.global.actions.SAcc;
import org.scribble.core.model.global.actions.SClientWrap;
import org.scribble.core.model.global.actions.SDisconnect;
import org.scribble.core.model.global.actions.SRecv;
import org.scribble.core.model.global.actions.SReq;
import org.scribble.core.model.global.actions.SSend;
import org.scribble.core.model.global.actions.SServerWrap;
import org.scribble.core.type.name.GProtoName;
import org.scribble.core.type.name.MsgId;
import org.scribble.core.type.name.RecVar;
import org.scribble.core.type.name.Role;
import org.scribble.core.type.session.Payload;

public interface ModelFactory
{
	EGraphBuilderUtil newEGraphBuilderUtil();
	SGraphBuilderUtil newSGraphBuilderUtil();

	ESend newESend(Role peer, MsgId<?> mid, Payload pay);
	ERecv newERecv(Role peer, MsgId<?> mid, Payload pay);
	EReq newEReq(Role peer, MsgId<?> mid, Payload pay);
	EAcc newEAcc(Role peer, MsgId<?> mid, Payload pay);
	EDisconnect newEDisconnect(Role peer);
	EClientWrap newEClientWrap(Role peer);
	EServerWrap newEServerWrap(Role peer);

	EState newEState(Set<RecVar> labs);
	//EFsm new EFsm(...)
	
	SSend newSSend(Role subj, Role obj, MsgId<?> mid, Payload pay);
	SRecv newSRecv(Role subj, Role obj, MsgId<?> mid, Payload pay);
	SReq newSReq(Role subj, Role obj, MsgId<?> mid, Payload pay);
	SAcc newSAcc(Role subj, Role obj, MsgId<?> mid, Payload pay);
	SDisconnect newSDisconnect(Role subj, Role obj);
	SClientWrap newSClientWrap(Role subj, Role obj);
	SServerWrap newSServerWrap(Role subj, Role obj);

	SState newSState(SConfig config);
	SConfig newSConfig(Map<Role, EFsm> state, SingleBuffers buffs);
	SGraph newSGraph(GProtoName proto, Map<Integer, SState> states, SState init);  // states: s.id -> s
	SModel newSModel(SGraph g);
}