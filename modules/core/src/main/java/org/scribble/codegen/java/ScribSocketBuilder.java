package org.scribble.codegen.java;

import org.scribble.model.local.EndpointState;
import org.scribble.sesstype.name.MessageId;
import org.scribble.sesstype.name.Role;

// Parameterize on output class type
public abstract class ScribSocketBuilder
{
	protected static final String SESSIONENDPOINT_CLASS = "org.scribble.net.session.SessionEndpoint";
	protected static final String BUFF_CLASS = "org.scribble.net.Buf";
	protected static final String OPENUM_INTERFACE = "org.scribble.net.session.OpEnum";

	protected static final String SENDSOCKET_CLASS = "org.scribble.net.scribsock.SendSocket";
	protected static final String RECEIVESOCKET_CLASS = "org.scribble.net.scribsock.ReceiveSocket";
	protected static final String BRANCHSOCKET_CLASS = "org.scribble.net.scribsock.BranchSocket";
	protected static final String CASESOCKET_CLASS = "org.scribble.net.scribsock.CaseSocket";
	protected static final String ENDSOCKET_CLASS = "org.scribble.net.scribsock.EndSocket";
	
	protected static final String BUFF_VAL_FIELD = "val";
	protected static final String SCRIBSOCKET_SE_FIELD = ClassBuilder.THIS + ".se";
	protected static final String SCRIBMESSAGE_PAYLOAD_FIELD = "payload";

	protected static final String RECEIVE_MESSAGE_PARAM = "m";
	protected static final String RECEIVE_ARG_PREFIX = "arg";

	protected static final String CASE_OP_FIELD = "op";
	protected static final String CASE_OP_PARAM = CASE_OP_FIELD;
	protected static final String CASE_MESSAGE_FIELD = "m";
	protected static final String CASE_MESSAGE_PARAM = CASE_MESSAGE_FIELD;
	protected static final String CASE_ARG_PREFIX = "arg";
	
	protected final StateChannelApiGenerator apigen;
	protected final EndpointState curr;
	protected final String className;

	protected final ClassBuilder cb = new ClassBuilder();
	
	public ScribSocketBuilder(StateChannelApiGenerator apigen, EndpointState curr)
	{
		this.apigen = apigen;
		this.curr = curr;
		this.className = getClassName();
	}
	
	protected String getClassName()
	{
		return this.apigen.getSocketClassName(this.curr);
	}

	public ClassBuilder build()
	{
		constructClass();  // So className can be "overridden" in subclass constructor (CaseSocket)
		return this.cb;
	}

	protected void constructClass()
	{
		constructClassExceptMethods();
		addMethods();
	}

	protected void constructClassExceptMethods()
	{
		this.cb.setName(this.className);
		//this.cb.setPackage(getSessionPackageName());
		this.cb.setPackage(getStateChannelPackageName());
		this.cb.addModifiers(ClassBuilder.PUBLIC, ClassBuilder.FINAL);
		//cb.setSuperClass(superc + "<" + SessionApiGenerator.getSessionClassName(this.gpn) + ", " + SessionApiGenerator.getRoleClassName(this.self) + ">");
		this.cb.setSuperClass(getSuperClassType());
		addImports();
		addConstructor();
	}
	
	protected abstract String getSuperClassType();

	protected void addImports()
	{
		this.cb.addImports("java.io.IOException");
		//this.cb.addImports(getSessionPackageName() + "." + getSessionClassName());
		this.cb.addImports(getEndpointApiRootPackageName() + ".*");
		this.cb.addImports(getRolesPackageName() + ".*");
	}
	
	protected MethodBuilder addConstructor()
	{
		final String SESSIONENDPOINT_PARAM = "se";
		String sess = getSessionClassName();
		String role = getSelfClassName();

		MethodBuilder ctor = cb.newConstructor(SESSIONENDPOINT_CLASS + "<" + sess + ", " + role + "> " + SESSIONENDPOINT_PARAM, "boolean dummy");
		ctor.addModifiers(ClassBuilder.PROTECTED);
		ctor.addBodyLine(ClassBuilder.SUPER + "(" + SESSIONENDPOINT_PARAM + ");");
		if (this.curr.equals(this.apigen.getInitialState()))
		{
			/*MethodBuilder mb = cb.newMethod("init");
			mb.addModifiers(ClassBuilder.PUBLIC, ClassBuilder.STATIC);
			mb.setReturn(this.root);
			mb.addParameters(SESSIONENDPOINT_CLASS + "<" + role + "> " + SESSIONENDPOINT_PARAM);
			mb.addExceptions(SCRIBBLERUNTIMEEXCEPTION_CLASS);
			mb.addBodyLine(SESSIONENDPOINT_PARAM + ".init();");
			mb.addBodyLine(ClassBuilder.RETURN + " " + ClassBuilder.NEW + " " + this.root + "(" + SESSIONENDPOINT_PARAM + ");");*/
			MethodBuilder ctor2 = cb.newConstructor(SESSIONENDPOINT_CLASS + "<" + sess + ", " + role + "> " + SESSIONENDPOINT_PARAM);
			ctor2.addExceptions(StateChannelApiGenerator.SCRIBBLERUNTIMEEXCEPTION_CLASS);
			ctor2.addModifiers(ClassBuilder.PUBLIC);
			ctor2.addBodyLine(ClassBuilder.SUPER + "(" + SESSIONENDPOINT_PARAM + ");");
			ctor2.addBodyLine(SESSIONENDPOINT_PARAM + ".init();");
		}
		return ctor;
	}
	
	protected abstract void addMethods();
	
	protected void setNextSocketReturnType(MethodBuilder mb, EndpointState succ)
	{
		if (succ.isTerminal())
		{
			mb.setReturn(ENDSOCKET_CLASS + "<" + getSessionClassName() + ", " + getSelfClassName() + ">");
		}
		else
		{
			mb.setReturn(this.apigen.getSocketClassName(succ));
		}
	}
	
	//protected void addReturnNextSocket(MethodBuilder mb, String nextClass)
	protected void addReturnNextSocket(MethodBuilder mb, EndpointState s)
	{
		String nextClass;
		//if (isTerminalClassName(nextClass))
		if (s.isTerminal())
		{
			mb.addBodyLine(SCRIBSOCKET_SE_FIELD + ".setCompleted();");  // Do before the IO action? in case of exception?
			nextClass = ENDSOCKET_CLASS + "<>";
		}
		else
		{
			nextClass = this.apigen.getSocketClassName(s);
		}
		mb.addBodyLine(ClassBuilder.RETURN + " " + ClassBuilder.NEW + " " + nextClass + "(" + SCRIBSOCKET_SE_FIELD + ", true);");
	}

	protected String getGarbageBuf(String futureClass)
	{
		//return ClassBuilder.NEW + " " + BUFF_CLASS + "<>()";  // Makes a trash Buff every time, but clean -- would be more efficient to generate the code to spawn the future without buff-ing it (partly duplicate of the normal receive generated code) 
		return "(" + BUFF_CLASS + "<" + futureClass + ">) " + SCRIBSOCKET_SE_FIELD + ".gc";  // FIXME: generic cast warning (this.ep.gc is Buff<?>) -- also retains unnecessary reference to the last created garbage future (but allows no-arg receive/async to be generated as simple wrapper call)
	}
	
	// Not fully qualified, just Session API class prefix
	// The constant singleton value of this type in the Session API (which is the same "name" as the class)
	protected String getSessionApiRoleConstant(Role role)
	{
		return SessionApiGenerator.getSessionClassName(this.apigen.getGProtocolName()) + "." + role.toString();
	}
	
	// Not fully qualified, just Session API class prefix
	// The constant singleton value of this type in the Session API (which is the same "name" as the class)
	protected String getSessionApiOpConstant(MessageId<?> mid)
	{
		return SessionApiGenerator.getSessionClassName(this.apigen.getGProtocolName()) + "." + SessionApiGenerator.getOpClassName(mid);
	}
	
	// Wrappers for EndpointApiGenerator getters
	protected String getSessionClassName()
	{
		return SessionApiGenerator.getSessionClassName(this.apigen.getGProtocolName());
	}
	
	protected String getSelfClassName()
	{
		return SessionApiGenerator.getRoleClassName(this.apigen.getSelf());
	}

	protected String getEndpointApiRootPackageName()
	{
		/*GProtocolName gpn = this.apigen.getGProtocolName();
		return SessionApiGenerator.getSessionApiPackageName(this.apigen.getGProtocolName()) + ".api" + gpn.getSimpleName();*/
		return SessionApiGenerator.getEndpointApiRootPackageName(this.apigen.getGProtocolName());
	}

	protected String getRolesPackageName()
	{
		return SessionApiGenerator.getRolesPackageName(this.apigen.getGProtocolName());
	}

	protected String getOpsPackageName()
	{
		return SessionApiGenerator.getOpsPackageName(this.apigen.getGProtocolName());
	}

	protected String getStateChannelPackageName()
	{
		//return getSessionPackageName() + ".channels." + this.apigen.getSelf();
		return SessionApiGenerator.getStateChannelPackageName(this.apigen.getGProtocolName(), this.apigen.getSelf());
	}
	
	/*private static boolean isTerminalClassName(String n)
	{
		//return n.equals(ClassBuilder.VOID);
		return n.equals(EndpointApiGenerator.ENDSOCKET_CLASS);
	}*/

	/*// Pre: not a terminal state (i.e. className is not void)
	private ClassBuilder constructInitClass(String className)
	{
		final String SESSIONENDPOINT_PARAM = "se";
		String role = SessionApiGenerator.getRoleClassName(this.self);

		ClassBuilder cb = new ClassBuilder();
		cb.setName(className);
		cb.setPackage(getPackageName());
		cb.setSuperClass(INITSOCKET_CLASS + "<" + role + ">");
		cb.addModifiers(ClassBuilder.PUBLIC);
		
		MethodBuilder ctor = cb.newConstructor(SESSIONENDPOINT_CLASS + "<" + role + "> " + SESSIONENDPOINT_PARAM);
		ctor.addModifiers(ClassBuilder.PUBLIC);
		ctor.addBodyLine(ClassBuilder.SUPER + "(" + SESSIONENDPOINT_PARAM + ");");
		
		MethodBuilder mb = cb.newMethod("init");
		mb.setReturn(this.root);
		mb.addModifiers(ClassBuilder.PUBLIC);
		mb.addExceptions(SCRIBBLERUNTIMEEXCEPTION_CLASS);
		mb.addBodyLine(ClassBuilder.SUPER + ".use();");  // Factor out
		//mb.addBodyLine(SCRIBSOCKET_SE_FIELD + ".init();");  // Factor out
		addReturnNextSocket(mb, this.root);

		return cb;
	}*/
}
