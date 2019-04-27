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
package org.scribble.core.model.endpoint;

import java.util.Set;

import org.scribble.core.model.ModelFactoryImpl;
import org.scribble.core.model.endpoint.actions.EAcc;
import org.scribble.core.model.endpoint.actions.EClientWrap;
import org.scribble.core.model.endpoint.actions.EDisconnect;
import org.scribble.core.model.endpoint.actions.ERecv;
import org.scribble.core.model.endpoint.actions.EReq;
import org.scribble.core.model.endpoint.actions.ESend;
import org.scribble.core.model.endpoint.actions.EServerWrap;
import org.scribble.core.type.name.MsgId;
import org.scribble.core.type.name.RecVar;
import org.scribble.core.type.name.Role;
import org.scribble.core.type.session.Payload;

// Separate E/SModelFactories fits protected E/SState constructor pattern
public class EModelFactoryImpl extends ModelFactoryImpl implements EModelFactory
{
	@Override
	public EGraphBuilderUtil newEGraphBuilderUtil()
	{
		return new EGraphBuilderUtil(this.mf);
	}

	@Override
	public EState newEState(Set<RecVar> labs)
	{
		return new EState(labs);
	}

	@Override
	public ESend newESend(Role peer, MsgId<?> mid, Payload pay)
	{
		return new ESend(this.mf, peer, mid, pay);
	}

	@Override
	public ERecv newERecv(Role peer, MsgId<?> mid, Payload pay)
	{
		return new ERecv(this.mf, peer, mid, pay);
	}

	@Override
	public EReq newEReq(Role peer, MsgId<?> mid, Payload pay)
	{
		return new EReq(this.mf, peer, mid, pay);
	}

	@Override
	public EAcc newEAcc(Role peer, MsgId<?> mid, Payload pay)
	{
		return new EAcc(this.mf, peer, mid, pay);
	}

	@Override
	public EDisconnect newEDisconnect(Role peer)
	{
		return new EDisconnect(this.mf, peer);
	}

	@Override
	public EClientWrap newEClientWrap(Role peer)
	{
		return new EClientWrap(this.mf, peer);
	}

	@Override
	public EServerWrap newEServerWrap(Role peer)
	{
		return new EServerWrap(this.mf, peer);
	}
}
