package org.scribble.ext.go.core.codegen.statetype;

import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import org.scribble.codegen.statetype.STSendActionBuilder;
import org.scribble.codegen.statetype.STStateChanApiBuilder;
import org.scribble.ext.go.core.model.endpoint.action.RPCoreEAction;
import org.scribble.ext.go.core.type.RPInterval;
import org.scribble.ext.go.core.type.RPIndexedRole;
import org.scribble.ext.go.main.GoJob;
import org.scribble.ext.go.type.index.RPIndexExpr;
import org.scribble.ext.go.type.index.RPIndexInt;
import org.scribble.ext.go.type.index.RPIndexVar;
import org.scribble.model.endpoint.EState;
import org.scribble.model.endpoint.actions.EAction;

public class ParamCoreSTSendActionBuilder extends STSendActionBuilder
{

	@Override
	public String getActionName(STStateChanApiBuilder api, EAction a)
	{
		return ParamCoreSTApiGenConstants.GO_CROSS_SEND_FUN_PREFIX + "_"
				+ ParamCoreSTStateChanApiBuilder.getGeneratedParamRoleName(((RPCoreEAction) a).getPeer())
				+ "_" + a.mid;
	}

	@Override
	public String buildArgs(STStateChanApiBuilder apigen, EAction a)
	{
		return IntStream.range(0, a.payload.elems.size()) 
					.mapToObj(i -> ParamCoreSTApiGenConstants.GO_CROSS_SEND_FUN_ARG
							+ i + " " + a.payload.elems.get(i)
							+ ", splitFn" + i + " func(" + ParamCoreSTApiGenConstants.GO_CROSS_SEND_FUN_ARG + i + " int, i" + i + " int) int"
							).collect(Collectors.joining(", "));
	}

	@Override
	public String buildBody(STStateChanApiBuilder api, EState curr, EAction a, EState succ)
	{
		String sEpWrite = 
				//s.ep.Write
				 ParamCoreSTApiGenConstants.GO_IO_FUN_RECEIVER + "." + ParamCoreSTApiGenConstants.GO_SCHAN_ENDPOINT
				 		+ "." + ParamCoreSTApiGenConstants.GO_ENDPOINT_ENDPOINT
						 + "." + ParamCoreSTApiGenConstants.GO_ENDPOINT_WRITEALL;
		String sEpProto =
				//"s.ep.Proto"
				ParamCoreSTApiGenConstants.GO_IO_FUN_RECEIVER + "."
					+ ParamCoreSTApiGenConstants.GO_SCHAN_ENDPOINT + "." + ParamCoreSTApiGenConstants.GO_ENDPOINT_PROTO;
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
				return ParamCoreSTApiGenConstants.GO_IO_FUN_RECEIVER + "."
					+ ParamCoreSTApiGenConstants.GO_SCHAN_ENDPOINT + ".Params[\"" + e + "\"]";
			}
			else
			{
				throw new RuntimeException("[param-core] TODO: " + e);
			}
		};
				
		String res =
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
				//+ ".(*" + api.gpn.getSimpleName() +")"
				+ "." + r.getName() + ", "
						+ foo.apply(g.start) + ", " + foo.apply(g.end) + ", "
								//+ "\"" + a.mid + "\""
								+ "b"
						+ ")\n";
				/*+ IntStream.range(0, a.payload.elems.size())
				      .mapToObj(i -> sEpWrite + "(" + sEpProto
				      				//+ ".(*" + api.gpn.getSimpleName() +")."
				      		+ r.getName() + ", "
									+ foo.apply(g.start) + ", " + foo.apply(g.end) + ", "
				      		+ "arg" + i + ")")
	 			      .collect(Collectors.joining("\n")) + "\n"*/
				/*+ "if " + sEpErr + " != nil {\n"
				+ "return nil\n"
				+ "}\n"*/
			}
				
		return
					res
				+ buildReturn(api, curr, succ);
	}
}