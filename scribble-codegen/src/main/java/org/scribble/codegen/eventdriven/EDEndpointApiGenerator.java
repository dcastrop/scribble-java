package org.scribble.codegen.eventdriven;

import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import org.scribble.ast.Module;
import org.scribble.ast.global.GProtocolDecl;
import org.scribble.codegen.java.endpointapi.SessionApiGenerator;
import org.scribble.codegen.java.util.ClassBuilder;
import org.scribble.del.ModuleDel;
import org.scribble.main.Job;
import org.scribble.main.JobContext;
import org.scribble.main.ScribbleException;
import org.scribble.model.MState;
import org.scribble.model.endpoint.EState;
import org.scribble.model.endpoint.EStateKind;
import org.scribble.model.endpoint.actions.EAction;
import org.scribble.type.kind.Kind;
import org.scribble.type.name.DataType;
import org.scribble.type.name.GProtocolName;
import org.scribble.type.name.MessageId;
import org.scribble.type.name.PayloadElemType;
import org.scribble.type.name.Role;
import org.scribble.visit.util.MessageIdCollector;

// From ParamCoreEndpointApiGenerator
public class EDEndpointApiGenerator
{
	public final Job job;
	public final GProtocolName proto;
	public final Role self;  // FIXME: base endpoint API gen is role-oriented, while session API generator should be neutral
	
	public EDEndpointApiGenerator(Job job, GProtocolName fullname, Role self)
	{
		this.job = job;
		this.proto = fullname;
		this.self = self;
	}

	// N.B. the base EGraph class will probably be replaced by a more specific (and more helpful) param-core class later
	public Map<String, String> build() throws ScribbleException
	{
		Map<String, String> res = new HashMap<>();  // filepath -> source 
		res.putAll(buildSessionApi());
		return res;
	}

	public Map<String, String> buildSessionApi() throws ScribbleException // FIXME: factor out
	{
		this.job.debugPrintln("\n[param-core] Running " + EDEndpointApiGenerator.class + " for " + this.proto + "@" + this.self);

		Map<String, String> res = new HashMap<>();
		res.putAll(new EDSessionApiBuilder(this.job, this.proto).generateApi());
		res.putAll(buildEndpointClass());
		return res;
	}
	
	public Map<String, String> buildEndpointClass() throws ScribbleException
	{
		JobContext jc = this.job.getContext();
		EState init = (this.job.minEfsm ? jc.getMinimisedEGraph(this.proto, this.self) : jc.getEGraph(this.proto, this.self)).init;  // FIXME: factor out with StateChannelApiGenerator constructor
		Set<EState> states = new HashSet<>();
		states.add(init);
		states.addAll(MState.getReachableStates(init));

		// frontend handler class
		String pack = SessionApiGenerator.getEndpointApiRootPackageName(this.proto);
		String name = this.proto.getSimpleName() + "_" + this.self;
		String sess = pack + "." + this.proto.getSimpleName();
		String role = SessionApiGenerator.getRolesPackageName(this.proto) + "." + this.self;
		String epClass = "";
		
		epClass += "package " + pack + ".handlers." + this.self + ";\n";
		epClass += "\n";
		/*epClass += "import java.util.function.Function;\n";
		epClass += "import java.util.HashMap;\n";
		epClass += "import java.util.Map;\n";*/
		epClass += "\n";
		epClass += "public class " + name + " extends org.scribble.runtime.net.session.EventDrivenEndpoint<" + sess + ", " + role + "> {\n";

		/*epClass += "private final Map<Object, Function<Object, org.scribble.runtime.net.ScribMessage>> outputs = new HashMap<>();\n";
		epClass += "\n";*/

		epClass += "public " + name + "(" + sess  + " sess, " + role
				+ " self, org.scribble.runtime.net.ScribMessageFormatter smf) throws java.io.IOException, org.scribble.main.ScribbleRuntimeException {\n";
		epClass += "super(sess, self, smf, " + pack + ".handlers.states." + this.self + "." + name + "_" + init.id + ".id" + ");\n";  // FIXME: factor out
		epClass += "}\n";
		epClass += "\n";
		
		/*epClass += "public enum State {" + states.stream().map(s -> getEDStateEnum(this.proto, this.self, s)) + "}\n";
		epClass += "\n";*/

		epClass += states.stream().map(s -> generateRegister(this.proto, this.self, s)).collect(Collectors.joining("\n"));
		/*epClass += "public void register(State s, Function<Object, org.scribble.runtime.net.ScribMessage> h) {\n";
		epClass += "this.outputs.put(s, h)";
		epClass += "}\n";
		epClass += "\n";
		epClass += "public void register(State s, Function<Object, org.scribble.runtime.net.ScribMessage> h) {\n";
		epClass += "this.outputs.put(s, h)";
		epClass += "}\n";*/
		
		epClass += "}\n";
		
		Map<String, String> res = new HashMap<>();
		String prefix = SessionApiGenerator.getEndpointApiRootPackageName(this.proto).replace('.', '/') + "/handlers/" + this.self + "/";  // StateChannelApiGenerator#generateApi
		res.put(prefix + name + ".java", epClass);
		
		// states
		String sprefix = SessionApiGenerator.getEndpointApiRootPackageName(this.proto).replace('.', '/') + "/handlers/states/" + this.self + "/";  // StateChannelApiGenerator#generateApi
		for (EState s : states)
		{
			EStateKind kind = s.getStateKind();
			String stateId = (kind == EStateKind.TERMINAL) ? "End" : name + "_" + s.id;
			String stateKind;
			switch (kind)
			{
				case OUTPUT:     stateKind = "org.scribble.runtime.net.state.ScribOutputState"; break;
				case UNARY_INPUT:
				case POLY_INPUT: stateKind = "org.scribble.runtime.net.state.ScribInputState";  break;
				case TERMINAL:   stateKind = "org.scribble.runtime.net.state.ScribEndState";    break;
				case ACCEPT:
				case WRAP_SERVER:
					throw new RuntimeException("TODO");
				default:
					throw new RuntimeException("TODO");
			}
			String stateClass = "";
			stateClass += "package " + pack + ".handlers.states." + this.self + ";\n";
			stateClass += "\n";
			stateClass += "public final class " + stateId + " extends " + stateKind + " {\n";
			stateClass += "public static final " + stateId + " id = new " + stateId + "("
					+ ((kind == EStateKind.UNARY_INPUT || kind == EStateKind.POLY_INPUT) ? SessionApiGenerator.getEndpointApiRootPackageName(this.proto) + ".roles." + s.getActions().get(0).peer + "." + s.getActions().get(0).peer : "")
					+ ");\n";
			stateClass += "private " + stateId + "("
					+ ((kind == EStateKind.UNARY_INPUT || kind == EStateKind.POLY_INPUT) ? "org.scribble.type.name.Role peer" : "")
					+ ") {\n";
			stateClass += ((kind == EStateKind.UNARY_INPUT || kind == EStateKind.POLY_INPUT) ? "super(\"" + stateId + "\", peer);" : "super(\"" + stateId + "\");") + "\n";
			for (EAction a : s.getAllActions())
			{
				stateClass += "this.succs.put(" + SessionApiGenerator.getEndpointApiRootPackageName(this.proto) + ".ops." + SessionApiGenerator.getOpClassName(a.mid) + "." + SessionApiGenerator.getOpClassName(a.mid)
						+ ", " + ((s.getSuccessor(a).getStateKind() == EStateKind.TERMINAL) ? "End" : this.proto.getSimpleName() + "_" + this.self + "_" + s.getSuccessor(a).id) + ".id);\n";
			}
			stateClass += "}\n";
			stateClass += "}\n";
			res.put(sprefix + stateId + ".java", stateClass);
			
			// messages
			if (s.getStateKind() == EStateKind.OUTPUT)
			{
				String mprefix = SessionApiGenerator.getEndpointApiRootPackageName(this.proto).replace('.', '/') + "/handlers/states/" + this.self + "/messages/";
				
				String messageIfName = name + "_" + s.id + "_Message";
				String messageInterface = "";
				messageInterface += "package " + pack + ".handlers.states." + this.self + ".messages;\n";
				messageInterface += "\n";
				messageInterface += "public interface " + messageIfName + " extends org.scribble.runtime.net.state.ScribHandlerMessage {\n";
				messageInterface += "}\n";
				res.put(mprefix + messageIfName + ".java", messageInterface);

				for (EAction a : s.getAllActions())
				{
					String messageName = name + "_" + s.id + "_" + SessionApiGenerator.getOpClassName(a.mid);
					String messageClass = "";
					messageClass += "package " + pack + ".handlers.states." + this.self + ".messages;\n";
					messageClass += "\n";
					messageClass += "public class " + messageName + " implements " + messageIfName + " {\n";
					messageClass += "public final java.util.List<Object> pay = new java.util.LinkedList<>();\n";
					messageClass += "public " + messageName + "(" + SessionApiGenerator.getEndpointApiRootPackageName(this.proto) + ".roles." + a.peer + " role";
					int i = 1;
					for (PayloadElemType<?> pet : a.payload.elems)
					{
						DataType dt = (DataType) pet;
						messageClass += ", " + dt + " arg" + i++;
					}
					messageClass += ") {\n";
					for (int j = 1; j <= a.payload.elems.size(); j++)
					{
						messageClass += "this.pay.add(arg" + j + ");\n";
					}
					messageClass += "}\n";
					messageClass += "\n";
					messageClass += "@Override\n";
					messageClass += "public org.scribble.type.name.Role getPeer() {\n";
					messageClass += "return " + SessionApiGenerator.getEndpointApiRootPackageName(this.proto) + ".roles." + a.peer + "." + a.peer + ";\n";
					messageClass += "}\n";
					messageClass += "\n";
					messageClass += "@Override\n";
					messageClass += "public org.scribble.type.name.Op getOp() {\n";
					messageClass += "return " + SessionApiGenerator.getEndpointApiRootPackageName(this.proto) + ".ops." + SessionApiGenerator.getOpClassName(a.mid) + "." + SessionApiGenerator.getOpClassName(a.mid) + ";\n";
					messageClass += "}\n";
					messageClass += "\n";
					messageClass += "@Override\n";
					messageClass += "public java.util.List<Object> getPayload() {\n";
					messageClass += "return this.pay;\n";
					messageClass += "}\n";
					messageClass += "}\n";
					res.put(mprefix + messageName + ".java", messageClass);
				}
			}
			
			// branches
			if (s.getStateKind() == EStateKind.UNARY_INPUT || s.getStateKind() == EStateKind.POLY_INPUT)
			{
				String bprefix = SessionApiGenerator.getEndpointApiRootPackageName(this.proto).replace('.', '/') + "/handlers/" + this.self + "/";
				String branchName = name + "_" + s.id + "_Branch";
				String branchInterface = "";
				branchInterface += "package " + pack + ".handlers." + this.self + ";\n";
				branchInterface += "";
				branchInterface += "public abstract class " + branchName + " implements org.scribble.runtime.net.state.ScribBranch {\n";
				for (EAction a : s.getAllActions())
				{
					branchInterface += "\npublic abstract void receive(" + SessionApiGenerator.getEndpointApiRootPackageName(this.proto) + ".ops." + SessionApiGenerator.getOpClassName(a.mid) + " op"; 
					int i = 1;
					for (PayloadElemType<?> pet : a.payload.elems)
					{
						DataType dt = (DataType) pet;
						branchInterface += ", " + dt + " arg" + i++;
					}
					branchInterface += ");\n";
				}

				branchInterface += "\n";
				branchInterface += "@Override\n";
				branchInterface += "public void dispatch(org.scribble.runtime.net.ScribMessage m) {\n";
				branchInterface += "switch (m.op.toString()) {\n";
				for (EAction a : s.getAllActions())
				{
					branchInterface += "case \"" + SessionApiGenerator.getOpClassName(a.mid) + "\": receive(";
					branchInterface += "(" + SessionApiGenerator.getEndpointApiRootPackageName(this.proto) + ".ops." + SessionApiGenerator.getOpClassName(a.mid) + ") m.op";
					int i = 0;
					for (PayloadElemType<?> pet : a.payload.elems)
					{
						DataType dt = (DataType) pet;
						branchInterface += ", (" + dt + ") m.payload[" + i++ + "]";
					}
					branchInterface += "); break;\n";
				}
				branchInterface += "default: throw new RuntimeException(\"Shouldn't get in here: \" + m);\n";
				branchInterface += "}\n";
				branchInterface += "}\n";
				branchInterface += "}\n";

				res.put(bprefix + branchName + ".java", branchInterface);
			}
		}
		
		/*// SessionApiGenerator#constructOpClasses
		Module mod = this.job.getContext().getModule(this.proto.getPrefix());
		GProtocolName simpname = this.proto.getSimpleName();
		GProtocolDecl gpd = (GProtocolDecl) mod.getProtocolDecl(simpname);
		MessageIdCollector coll = new MessageIdCollector(this.job, ((ModuleDel) mod.del()).getModuleContext());
		gpd.accept(coll);
		for (MessageId<?> mid : coll.getNames())
		{
			String messageName = SessionApiGenerator.getOpClassName(mid);
			String messageClass = "";
			messageClass += "package " + pack + ".handlers.messages;\n";
			messageClass += "\n";
			messageClass += "public class " + messageName + " {\n";
			messageClass += "public final java.util.List<Object> pay = new java.util.LinkedList<>();\n";
			messageClass += "public " + messageName + "(" + + ")";
			messageClass += "}\n";
			res.put(prefix + messageName + ".java", messageClass);
		}*/
		
		return res;
	}

  /*// cf. StateChannelApiGenerator#newSocketClassName
	public static String getEDStateEnum(GProtocolName gpn, Role self, EState s)
	{
		return gpn.getSimpleName() + "_" + self + "_" + s.id;
	}*/

	private String generateRegister(GProtocolName gpn, Role self, EState s)
	{
		String prefix = SessionApiGenerator.getEndpointApiRootPackageName(this.proto) + ".handlers.states." + this.self + "." ;
		String res = "";
		String name = gpn.getSimpleName() + "_" + self;
		switch (s.getStateKind())
		{
			case OUTPUT:
			{
				// FIXME: "untyped" (ScribEvent) -- need state-specific "enums"
				res += "public void register(" + prefix + name + "_" + s.id
						+ " sid, java.util.function.Function<Object, "
						+ SessionApiGenerator.getEndpointApiRootPackageName(this.proto) + ".handlers.states." + this.self + ".messages." + name + "_" + s.id + "_Message> h) {\n";  // FIXME: factor out
				res += "this.outputs.put(sid, h);\n";
				res += "}\n";
				break;
			}
			case UNARY_INPUT:
			case POLY_INPUT:
			{
				res += "public void register(" + prefix + name + "_" + s.id + " sid";
				/*for (EAction a : s.getAllActions())
				{
					res += ", org.scribble.util.function.Function2<" + SessionApiGenerator.getEndpointApiRootPackageName(this.proto) + ".ops." + SessionApiGenerator.getOpClassName(a.mid)
							+ ", Object"
							+ ", Void> h_" + a.mid;
				}
				res += "java.util.Map<org.scribble.type.name.Op, org.scribble.util.function.Function2<? extends org.scribble.type.name.Op, Object, Void>> tmp = this.inputs.get(sid);\n";
				res += "if (tmp == null) {\n";
				res += "tmp = new java.util.HashMap<>();\n";
				res += "this.inputs.put(sid, tmp);\n";
				for (EAction a : s.getAllActions())
				{
					res += "tmp.put(" + SessionApiGenerator.getEndpointApiRootPackageName(this.proto) + ".ops." + SessionApiGenerator.getOpClassName(a.mid) + "." + SessionApiGenerator.getOpClassName(a.mid) + ", h_" + a.mid + ");\n";
				}
				res += "}\n";*/
				res += ", " + SessionApiGenerator.getEndpointApiRootPackageName(this.proto) + ".handlers." + this.self + "." + name + "_" + s.id + "_Branch b";
				res += ") {\n";
				res += "this.inputs.put(sid, b);\n";
				res += "}\n";
				break;
			}
			case TERMINAL:
			{
				break;
			}
			case ACCEPT:
			case WRAP_SERVER:
			{
				throw new RuntimeException("[scrib] TODO: " + s);
			}
			default:
			{
				throw new RuntimeException("[scrib] Shouldn't get in here: " + s);
			}
		}
		return res;
	}

	/*public String generateRootPackageDecl()
	{
		return "package " + getRootPackage();
	}
	
	private String getRootPackage()  // Derives only from proto name
	{
		//throw new RuntimeException("[param-core] TODO:");
		return this.proto.getSimpleName().toString();
	}*/

	public String generateScribbleRuntimeImports()
	{
		return getScribbleRuntimeImports().stream().map(x -> "import \"" + x + "\"\n").collect(Collectors.joining());
	}

	private List<String> getScribbleRuntimeImports()  // FIXME: factor up
	{
		return Stream.of(
					//EDApiGenConstants.GO_SCRIBBLERUNTIME_SESSION_PACKAGE
				""
				).collect(Collectors.toList());
	}
}
