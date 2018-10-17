package org.scribble.ext.go.core.codegen.statetype3;

import java.util.List;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import org.scribble.codegen.statetype.STSendActionBuilder;
import org.scribble.codegen.statetype.STStateChanApiBuilder;
import org.scribble.ext.go.core.model.endpoint.action.RPCoreEAction;
import org.scribble.ext.go.core.type.RPIndexedRole;
import org.scribble.ext.go.core.type.RPInterval;
import org.scribble.ext.go.type.index.RPIndexExpr;
import org.scribble.ext.go.type.index.RPIndexInt;
import org.scribble.ext.go.type.index.RPIndexVar;
import org.scribble.model.endpoint.EState;
import org.scribble.model.endpoint.actions.EAction;
import org.scribble.type.name.DataType;
import org.scribble.type.name.PayloadElemType;

public class RPCoreSTSplitActionBuilder extends STSendActionBuilder
{

	@Override
	public String getActionName(STStateChanApiBuilder api, EAction a)
	{
		return RPCoreSTApiGenConstants.GO_CROSS_SPLIT_FUN_PREFIX + "_"
				+ RPCoreSTStateChanApiBuilder.getGeneratedIndexedRoleName(((RPCoreEAction) a).getPeer())
				+ "_" + a.mid;
	}

	@Override
	public String buildArgs(STStateChanApiBuilder apigen, EAction a)
	{
		RPCoreSTStateChanApiBuilder api = (RPCoreSTStateChanApiBuilder) apigen;
		//DataType[] pet = new DataType[1];
		PayloadElemType[] pet = new PayloadElemType[1];
		return IntStream.range(0, a.payload.elems.size()) 
					.mapToObj(i -> RPCoreSTApiGenConstants.GO_CROSS_SEND_METHOD_ARG
							+ i + " "
							
											// HACK
									+ ((api.isDelegType(pet[0] = a.payload.elems.get(i))) ? "*" : "")
									+ api.getPayloadElemTypeName(pet[0]) //a.payload.elems.get(i)

							+ ", splitFn" + i + " func(" + RPCoreSTApiGenConstants.GO_CROSS_SEND_METHOD_ARG + i + " "

											// HACK
									+ (api.isDelegType(pet[0]) ? "*" : "")
									+ api.getPayloadElemTypeName(pet[0])

									+ ", i" + i + " int) "
									
									+ (api.isDelegType(pet[0]) ? "*" : "")
									+ api.getPayloadElemTypeName(pet[0])

							).collect(Collectors.joining(", "));
	}

	@Override
	public String buildBody(STStateChanApiBuilder api, EState curr, EAction a, EState succ)
	{
		if(a.payload.elems.size() > 1)
		{
			throw new RuntimeException("[param-core] TODO: " + a);
		}

		List<EAction> as = curr.getActions();
		if (as.size() > 1 && as.stream().anyMatch(b -> b.mid.toString().equals("")))  // HACK
		{
			throw new //ParamCoreException
					RuntimeException("[param-core] Empty labels not allowed in non-unary choices: " + curr.getActions());
		}

		String sEpWrite = 
				//s.ep.Write
				 RPCoreSTApiGenConstants.GO_IO_METHOD_RECEIVER + "." + RPCoreSTApiGenConstants.GO_SCHAN_ENDPOINT
				 		+ "." + RPCoreSTApiGenConstants.GO_MPCHAN_SESSCHAN
						//+ "." + ParamCoreSTApiGenConstants.GO_ENDPOINT_WRITEALL;
						+ ".Conn";
		String sEpProto =
				//"s.ep.Proto"
				RPCoreSTApiGenConstants.GO_IO_METHOD_RECEIVER + "."
					+ RPCoreSTApiGenConstants.GO_SCHAN_ENDPOINT + "." + RPCoreSTApiGenConstants.GO_MPCHAN_PROTO;
		/*String sEpErr =
				//"s.ep.Err"
				ParamCoreSTApiGenConstants.GO_IO_FUN_RECEIVER + "."
					+ ParamCoreSTApiGenConstants.GO_SCHAN_ENDPOINT + "." + ParamCoreSTApiGenConstants.GO_ENDPOINT_ERR;*/

		RPIndexedRole r = (RPIndexedRole) a.peer;
		RPInterval g = r.intervals.iterator().next();
		Function<RPIndexExpr, String> foo = e ->
		{
			if (e instanceof RPIndexInt)
			{
				return e.toString();
			}
			else if (e instanceof RPIndexVar)
			{
				return RPCoreSTApiGenConstants.GO_IO_METHOD_RECEIVER + "."
					+ RPCoreSTApiGenConstants.GO_SCHAN_ENDPOINT + ".Params[\"" + e + "\"]";
			}
			else
			{
				throw new RuntimeException("[param-core] TODO: " + e);
			}
		};
				
		/*String res =
					(((GoJob) api.job).noCopy
				?
				  "labels := make([]interface{}, " + foo.apply(g.end) + "-" + foo.apply(g.start) + "+1)\n"
				+ "for i := " + foo.apply(g.start) + "; i <= " + foo.apply(g.end) + "; i++ {\n"
						+ "tmp := \"" + a.mid + "\"\n"
						+ "\tlabels[i-" + foo.apply(g.start) + "] = &tmp\n"
				+ "}\n"
				:
				  "labels := make([][]byte, " + foo.apply(g.end) + "-" + foo.apply(g.start) + "+1)\n"
				+ "for i := " + foo.apply(g.start) + "; i <= " + foo.apply(g.end) + "; i++ {\n"
						+ "\tlabels[i-" + foo.apply(g.start) + "] = []byte(\"" + a.mid + "\")\n"
				+ "}\n")

				+ sEpWrite + (((GoJob) api.job).noCopy ? "Raw" : "")
						+ "(" + sEpProto + "." + r.getName() + ", "
						+ foo.apply(g.start) + ", " + foo.apply(g.end) + ", "
						+ "labels)\n";

			if (!a.payload.elems.isEmpty())
			{
				if (a.payload.elems.size() > 1)
				{
					throw new RuntimeException("[param-core] [TODO] payload size > 1: " + a);
				}
				res +=
				  (((GoJob) api.job).noCopy
				?
				  "b := make([]interface{}, " + foo.apply(g.end) + "-" + foo.apply(g.start) + "+1)\n"
				+ "for i := " + foo.apply(g.start) + "; i <= " + foo.apply(g.end)+"; i++ {\n"
						+ "tmp := splitFn0(arg0, i)\n"
						+ "\tb[i-"+foo.apply(g.start)+"] = &tmp\n"
				+ "}\n"
				:
				  "b := make([][]byte, " + foo.apply(g.end) + "-" + foo.apply(g.start) + "+1)\n"
				+ "for i := " + foo.apply(g.start) + "; i <= "+foo.apply(g.end)+"; i++ {\n"
						+ "\tvar buf bytes.Buffer\n"
						+ "\tif err := gob.NewEncoder(&buf).Encode(splitFn0(arg0, i)); err != nil {\n\t\t" // only arg0
						+ ParamCoreSTApiGenConstants.GO_IO_FUN_RECEIVER + "."
								+ ParamCoreSTApiGenConstants.GO_SCHAN_ENDPOINT + "." + ParamCoreSTApiGenConstants.GO_ENDPOINT_ENDPOINT
								+ ".Errors <- session.SerialiseFailed(err, \"" + getActionName(api, a) +"\", "
								+ ParamCoreSTApiGenConstants.GO_IO_FUN_RECEIVER + "."
								+ ParamCoreSTApiGenConstants.GO_SCHAN_ENDPOINT + "." + ParamCoreSTApiGenConstants.GO_ENDPOINT_ENDPOINT
								+ ".Self.Name())\n"
						+ "\t}\n"
						+ "\tb[i-"+foo.apply(g.start)+"] = buf.Bytes()\n"
				+ "}\n")
				
				+ sEpWrite + (((GoJob) api.job).noCopy ? "Raw" : "")
				+ "(" + sEpProto
				+ "." + r.getName() + ", "
						+ foo.apply(g.start) + ", " + foo.apply(g.end) + ", "
								//+ "\"" + a.mid + "\""
								+ "b"
						+ ")\n";
			}*/

		String res =
			//st1.Use()
				"for i := " + foo.apply(g.start) + "; i <= "+foo.apply(g.end)+"; i++ {\n"

				//+ ParamCoreSTApiGenConstants.GO_IO_FUN_RECEIVER + "." + ParamCoreSTApiGenConstants.GO_SCHAN_ENDPOINT
				+ (a.mid.toString().equals("") ? "" :  // HACK
					"if err := " + sEpWrite
						+ "[" +  sEpProto + "." + r.getName() + ".Name()][i]"
						+ "." + RPCoreSTApiGenConstants.GO_MPCHAN_WRITEALL
						+ "(" //+ sEpProto + "." + r.getName() + ", "
						+ "\"" + a.mid + "\"" + "); err != nil {\n"
						+ "log.Fatal(err)\n"
						+ "}\n")
						
				+ ((((RPCoreSTStateChanApiBuilder) api).isDelegType((DataType) a.payload.elems.get(0))) ? "arg0.Res.Use()\n" : "")

				//+ ParamCoreSTApiGenConstants.GO_IO_FUN_RECEIVER + "." + ParamCoreSTApiGenConstants.GO_SCHAN_ENDPOINT
				+ "if err := " + sEpWrite
						+ "[" +  sEpProto + "." + r.getName() + ".Name()][i]"
						+ "." + RPCoreSTApiGenConstants.GO_MPCHAN_WRITEALL
						+ "(" //+ sEpProto + "." + r.getName() + ", "
						
						+ "splitFn0(arg0, i)" + "); err != nil {\n"
						+ "log.Fatal(err)\n"
						+ "}\n"
				+ "}\n";

			/*for i, v := range pl {
				st1.ept.Conn[Worker][i].Send(a.mid)
				st1.ept.Conn[Worker][i].Send(v)
			}*/
				
		return
					res
				+ buildReturn(api, curr, succ);
	}
}
